//! Integration tests for the hbbs KeyExchange encrypted handshake.
//!
//! The tests play the "official client" role with byte-level fidelity, using the same
//! hbb_common primitives the client uses (see rustdesk/src/common.rs `key_exchange`):
//!   1. v1 handshake succeeds, the stream is secured and round-trips encrypted frames
//!   2. wire frames after the handshake are really unreadable without the derived key
//!   3. legacy/unlogged clients that skip the KeyExchange frame stay on plaintext
//!   4. `KEY_EXCHANGE=N` restores the old server-first-nothing behaviour
//!   5. tampered handshake replies (wrong key count / broken seal) are rejected by
//!      dropping the connection instead of falling back to plaintext

use hbb_common::{
    bytes::BytesMut,
    protobuf::Message,
    rendezvous_proto::{
        rendezvous_message, KeyExchange, KxParams, RendezvousMessage, TestNatRequest,
    },
    tcp::{Encrypt, FramedStream, KxTranscript, KX_PARAMS_DOMAIN},
    tokio::{io::{AsyncReadExt, AsyncWriteExt}, net::TcpStream, time::Duration},
    timeout,
};
use hbbs::RendezvousServer;
use once_cell::sync::Lazy;
use sodiumoxide::crypto::{box_, secretbox, sign};

/// Distinct fixed ports per test so servers can run concurrently; hbbs also binds
/// port-1 (NAT test) and port+2 (websocket) beside the main port.
const PORT_KX_ON: u16 = 41161;
const PORT_WIRE: u16 = 41171;
const PORT_LEGACY: u16 = 41181;
const PORT_DISABLED: u16 = 41191;
const PORT_TAMPER: u16 = 41201;

/// Serializes the env-mutating server spawns: every env var the server consumes at
/// startup is read before its listeners come up, so "the port accepts" is a clean
/// synchronization point for restoring the environment afterwards.
static SPAWN_LOCK: Lazy<std::sync::Mutex<()>> = Lazy::new(|| std::sync::Mutex::new(()));

/// hbbs' UDP self-test is pointless (and fatal via `process::exit` on failure) under
/// tests; disable it for the whole test binary, which no test ever overrides. Also
/// start a logger so the spawned servers' log lines are visible on stderr.
static TEST_ENV: Lazy<()> = Lazy::new(|| {
    std::env::set_var("TEST_HBBS", "no");
    let _ = flexi_logger::Logger::try_with_str("debug")
        .unwrap()
        .start();
});

/// Drive an async test body on a current-thread runtime; avoids depending on the
/// `tokio::test` attribute macro, which needs a direct tokio link in the test crate.
fn block_on<F: std::future::Future>(fut: F) -> F::Output {
    hbb_common::tokio::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .unwrap()
        .block_on(fut)
}

struct TestServer {
    port: u16,
    rs_pk_bytes: Vec<u8>,
}

impl TestServer {
    fn rs_pk(&self) -> sign::PublicKey {
        sign::PublicKey::from_slice(&self.rs_pk_bytes).unwrap()
    }
}

/// Spawn a real hbbs on 127.0.0.1:port with a fresh ed25519 keypair and its own sqlite
/// file, and wait until the main TCP port accepts (i.e. startup env was consumed).
fn spawn_server(port: u16, key_exchange: bool) -> TestServer {
    *TEST_ENV;
    let dir = format!("/tmp/kx-handshake-test-{port}");
    std::fs::create_dir_all(&dir).unwrap();
    let (pk, sk) = sign::gen_keypair();
    let sk_b64 = base64::encode(&sk.0);
    let guard = SPAWN_LOCK.lock().unwrap();
    let prev = std::env::var("KEY_EXCHANGE").ok();
    std::env::set_var("KEY_EXCHANGE", if key_exchange { "Y" } else { "N" });
    std::env::set_var("DB_URL", format!("{dir}/db_v2.sqlite3"));
    let _handle = std::thread::spawn(move || {
        RendezvousServer::start_with_bind(
            Some(std::net::IpAddr::from([127u8, 0, 0, 1])),
            port as i32,
            1,
            &sk_b64,
            0,
        )
        .expect("hbbs exited with error");
    });
    let mut ready = false;
    for _ in 0..300 {
        if std::net::TcpStream::connect(("127.0.0.1", port)).is_ok() {
            ready = true;
            break;
        }
        std::thread::sleep(Duration::from_millis(100));
    }
    assert!(ready, "hbbs on port {port} did not come up in time");
    match prev {
        Some(v) => std::env::set_var("KEY_EXCHANGE", v),
        None => std::env::remove_var("KEY_EXCHANGE"),
    }
    std::env::remove_var("DB_URL");
    drop(guard);
    TestServer {
        port,
        rs_pk_bytes: pk.0.to_vec(),
    }
}

// ---------------------------------------------------------------------------
// Manual RustDesk frame codec (mirrors hbb_common BytesCodec): the length is
// shifted left by 2 bits and the low 2 bits of the first byte carry head_len-1.
// ---------------------------------------------------------------------------

fn encode_frame(data: &[u8]) -> Vec<u8> {
    let n = data.len();
    let mut out = Vec::with_capacity(n + 4);
    if n <= 0x3F {
        out.push((n << 2) as u8);
    } else if n <= 0x3FFF {
        out.extend_from_slice(&(((n << 2) as u16) | 0x1).to_le_bytes());
    } else if n <= 0x3FFFFF {
        let h = ((n as u32) << 2) | 0x2;
        out.extend_from_slice(&(h as u16).to_le_bytes());
        out.push((h >> 16) as u8);
    } else {
        panic!("frame too large for the test codec");
    }
    out.extend_from_slice(data);
    out
}

async fn read_frame(stream: &mut TcpStream) -> std::io::Result<Vec<u8>> {
    let mut head = [0u8; 1];
    stream.read_exact(&mut head).await?;
    let head_len = ((head[0] & 0x3) + 1) as usize;
    let mut raw = vec![0u8; head_len];
    raw[0] = head[0];
    if head_len > 1 {
        stream.read_exact(&mut raw[1..]).await?;
    }
    let mut n = u32::from_le_bytes([
        raw[0],
        raw.get(1).copied().unwrap_or(0),
        raw.get(2).copied().unwrap_or(0),
        raw.get(3).copied().unwrap_or(0),
    ]) as usize;
    n >>= 2;
    let mut buf = vec![0u8; n];
    stream.read_exact(&mut buf).await?;
    Ok(buf)
}

// ---------------------------------------------------------------------------
// Client-side handshake helpers
// ---------------------------------------------------------------------------

/// Assert the frame is a server-first KeyExchange with exactly one ed25519 signature
/// over the ephemeral box public key (top bit set) and valid signed v1 parameters.
/// Returns the signed (top-bit-marked) box public key bytes.
fn verify_server_key_exchange(first: &[u8], rs_pk: &sign::PublicKey) -> Vec<u8> {
    let msg = RendezvousMessage::parse_from_bytes(first).expect("parse server first frame");
    let ex = match msg.union {
        Some(rendezvous_message::Union::KeyExchange(ex)) => ex,
        _ => panic!("server first frame is not a KeyExchange"),
    };
    assert_eq!(ex.keys.len(), 1, "server must send exactly one key");
    let signed_pk = sign::verify(&ex.keys[0], rs_pk).expect("signature mismatch on keys[0]");
    assert_eq!(signed_pk.len(), box_::PUBLICKEYBYTES);
    assert_ne!(
        signed_pk[31] & 0x80,
        0,
        "top bit of the signed box public key must be set"
    );
    let params_signed =
        sign::verify(&ex.signed_params, rs_pk).expect("signature mismatch on signed_params");
    let body = params_signed
        .strip_prefix(KX_PARAMS_DOMAIN)
        .expect("signed_params must carry the KxParams domain prefix");
    let params = KxParams::parse_from_bytes(body).expect("parse KxParams");
    assert_eq!(&params.pk[..], &signed_pk[..], "params.pk mismatch");
    assert_eq!(params.version, ex.version, "params.version mismatch");
    assert_eq!(ex.version, 1, "server must advertise v1");
    signed_pk
}

/// The client half of the sealed symmetric key (common.rs create_symmetric_key_msg):
/// client generates the stream key and seals it to the server's box public key with
/// an all-zero nonce.
fn client_symmetric_key_msg(signed_pk: &[u8]) -> (box_::PublicKey, secretbox::Key, Vec<u8>) {
    let (our_pk, our_sk) = box_::gen_keypair();
    let key = secretbox::gen_key();
    let server_box_pk = box_::PublicKey::from_slice(signed_pk).unwrap();
    let sealed_key = box_::seal(
        &key.0,
        &box_::Nonce([0u8; box_::NONCEBYTES]),
        &server_box_pk,
        &our_sk,
    );
    (our_pk, key, sealed_key)
}

fn client_transcript<'a>(our_pk: &'a box_::PublicKey, signed_pk: &'a [u8]) -> KxTranscript<'a> {
    KxTranscript {
        initiator_pk: &our_pk.0,
        responder_pk: signed_pk,
        advertised: 1,
        picked: 1,
    }
}

/// Replay the client side of the handshake over a `FramedStream` (exactly what
/// rustdesk/src/common.rs `key_exchange` does) and secure the client stream.
async fn client_key_exchange(
    stream: &mut FramedStream,
    rs_pk: &sign::PublicKey,
) -> secretbox::Key {
    let first = stream
        .next_timeout(10_000)
        .await
        .expect("no KeyExchange received")
        .expect("read first frame failed");
    let signed_pk = verify_server_key_exchange(&first, rs_pk);
    let (our_pk, key, sealed_key) = client_symmetric_key_msg(&signed_pk);
    let mut reply = RendezvousMessage::new();
    reply.set_key_exchange(KeyExchange {
        keys: vec![our_pk.0.to_vec().into(), sealed_key.into()],
        version: 1,
        ..Default::default()
    });
    stream.send(&reply).await.expect("send handshake reply");
    stream
        .set_key_split(key.clone(), true, &client_transcript(&our_pk, &signed_pk))
        .expect("set client split key");
    key
}

fn test_nat_request(serial: i32) -> RendezvousMessage {
    let mut msg = RendezvousMessage::new();
    msg.set_test_nat_request(TestNatRequest {
        serial,
        ..Default::default()
    });
    msg
}

fn expect_test_nat_response(bytes: &[u8], port: u16) {
    let msg = RendezvousMessage::parse_from_bytes(bytes).expect("parse TestNatResponse");
    match msg.union {
        Some(rendezvous_message::Union::TestNatResponse(r)) => {
            assert_eq!(r.port, port as i32, "reflected port mismatch");
        }
        _ => panic!("expected TestNatResponse, got something else"),
    }
}

// ---------------------------------------------------------------------------
// 1. v1 handshake success + secured stream + encrypted round-trip
// ---------------------------------------------------------------------------

#[test]
fn v1_handshake_secures_the_stream_and_roundtrips() {
    block_on(async {
        let server = spawn_server(PORT_KX_ON, true);
        let tcp = TcpStream::connect(("127.0.0.1", server.port)).await.unwrap();
        let local_port = tcp.local_addr().unwrap().port();
        let addr = tcp.peer_addr().unwrap();
        let mut stream = FramedStream::from(tcp, addr);

        let _key = client_key_exchange(&mut stream, &server.rs_pk()).await;
        assert!(stream.is_secured(), "stream must be secured after handshake");

        stream
            .send(&test_nat_request(4321))
            .await
            .expect("send encrypted TestNatRequest");
        let resp = stream
            .next_timeout(10_000)
            .await
            .expect("no response")
            .expect("read response failed");
        expect_test_nat_response(&resp, local_port);
    })
}

// ---------------------------------------------------------------------------
// 2. wire frames after the handshake are really encrypted (plaintext unreadable)
// ---------------------------------------------------------------------------

#[test]
fn wire_frames_after_handshake_are_encrypted() {
    block_on(async {
        let server = spawn_server(PORT_WIRE, true);
        let mut tcp = TcpStream::connect(("127.0.0.1", server.port)).await.unwrap();
        let local_port = tcp.local_addr().unwrap().port();

        // Plaintext phase over a raw socket with manual framing.
        let first = timeout(10_000, read_frame(&mut tcp))
            .await
            .expect("timeout reading first frame")
            .expect("read first frame failed");
        let signed_pk = verify_server_key_exchange(&first, &server.rs_pk());
        let (our_pk, key, sealed_key) = client_symmetric_key_msg(&signed_pk);
        let mut reply = RendezvousMessage::new();
        reply.set_key_exchange(KeyExchange {
            keys: vec![our_pk.0.to_vec().into(), sealed_key.into()],
            version: 1,
            ..Default::default()
        });
        tcp.write_all(&encode_frame(&reply.write_to_bytes().unwrap()))
            .await
            .unwrap();

        // Encrypted phase: client-side split encryptor, exactly like the client stream.
        let transcript = client_transcript(&our_pk, &signed_pk);
        let mut enc = Encrypt::new_split(key.clone(), true, &transcript).unwrap();
        let sealed_req = enc.enc(&test_nat_request(7).write_to_bytes().unwrap());
        tcp.write_all(&encode_frame(&sealed_req)).await.unwrap();

        // The response on the wire must NOT be parseable as plaintext TestNatResponse...
        let raw = timeout(10_000, read_frame(&mut tcp))
            .await
            .expect("timeout reading response")
            .expect("read response failed");
        let plaintext_ok = RendezvousMessage::parse_from_bytes(&raw)
            .ok()
            .and_then(|m| m.union)
            .map(|u| matches!(u, rendezvous_message::Union::TestNatResponse(_)))
            .unwrap_or(false);
        assert!(
            !plaintext_ok,
            "the response frame leaked plaintext TestNatResponse on the wire"
        );

        // ...but decrypting it with the derived receive key yields the real response.
        let mut dec = Encrypt::new_split(key, true, &transcript).unwrap();
        let mut buf = BytesMut::from(&raw[..]);
        dec.dec(&mut buf).expect("decrypt response");
        expect_test_nat_response(&buf, local_port);
    })
}

// ---------------------------------------------------------------------------
// 3. legacy/unlogged clients skip the KeyExchange frame and stay on plaintext
// ---------------------------------------------------------------------------

#[test]
fn legacy_client_skips_key_exchange_and_stays_plaintext() {
    block_on(async {
        let server = spawn_server(PORT_LEGACY, true);
        let tcp = TcpStream::connect(("127.0.0.1", server.port)).await.unwrap();
        let local_port = tcp.local_addr().unwrap().port();
        let addr = tcp.peer_addr().unwrap();
        let mut stream = FramedStream::from(tcp, addr);

        // Read and discard the server's KeyExchange offer, like get_next_nonkeyexchange_msg.
        let first = stream
            .next_timeout(10_000)
            .await
            .expect("no first frame")
            .expect("read first frame failed");
        let msg = RendezvousMessage::parse_from_bytes(&first).unwrap();
        assert!(matches!(
            msg.union,
            Some(rendezvous_message::Union::KeyExchange(_))
        ));

        // Plain TestNatRequest without any key must be served in plaintext.
        stream
            .send(&test_nat_request(0))
            .await
            .expect("send plaintext TestNatRequest");
        let resp = stream
            .next_timeout(10_000)
            .await
            .expect("no response")
            .expect("read response failed");
        expect_test_nat_response(&resp, local_port);
        assert!(
            !stream.is_secured(),
            "legacy connection must not be switched to encrypted"
        );
    })
}

// ---------------------------------------------------------------------------
// 4. KEY_EXCHANGE=N restores the old behaviour: server stays silent, plaintext only
// ---------------------------------------------------------------------------

#[test]
fn key_exchange_disabled_keeps_old_plaintext_behaviour() {
    block_on(async {
        let server = spawn_server(PORT_DISABLED, false);
        let tcp = TcpStream::connect(("127.0.0.1", server.port)).await.unwrap();
        let local_port = tcp.local_addr().unwrap().port();
        let addr = tcp.peer_addr().unwrap();
        let mut stream = FramedStream::from(tcp, addr);

        // The client speaks first; the very first frame back must be the response
        // itself, proving the server sent no KeyExchange offer.
        stream
            .send(&test_nat_request(0))
            .await
            .expect("send plaintext TestNatRequest");
        let resp = stream
            .next_timeout(10_000)
            .await
            .expect("no response")
            .expect("read response failed");
        expect_test_nat_response(&resp, local_port);
        assert!(!stream.is_secured());
    })
}

// ---------------------------------------------------------------------------
// 5. tampered handshake replies are rejected (connection dropped, no plaintext fallback)
// ---------------------------------------------------------------------------

#[test]
fn tampered_handshake_replies_are_rejected() {
    block_on(async {
        let server = spawn_server(PORT_TAMPER, true);

        // (a) wrong number of keys in the reply
        let mut tcp = TcpStream::connect(("127.0.0.1", server.port)).await.unwrap();
        let first = timeout(10_000, read_frame(&mut tcp))
            .await
            .expect("timeout reading first frame")
            .expect("read first frame failed");
        let signed_pk = verify_server_key_exchange(&first, &server.rs_pk());
        assert_ne!(signed_pk[31] & 0x80, 0);
        let mut bad_count = RendezvousMessage::new();
        bad_count.set_key_exchange(KeyExchange {
            keys: vec![vec![0u8; box_::PUBLICKEYBYTES].into()],
            version: 1,
            ..Default::default()
        });
        tcp.write_all(&encode_frame(&bad_count.write_to_bytes().unwrap()))
            .await
            .unwrap();
        let res = timeout(10_000, read_frame(&mut tcp)).await;
        assert!(
            res.is_err() || res.unwrap().is_err(),
            "server must close the connection on a 1-key reply"
        );
        drop(tcp);

        // (b) sealed key that cannot be opened with the server's ephemeral secret
        let mut tcp = TcpStream::connect(("127.0.0.1", server.port)).await.unwrap();
        let first = timeout(10_000, read_frame(&mut tcp))
            .await
            .expect("timeout reading first frame")
            .expect("read first frame failed");
        let signed_pk = verify_server_key_exchange(&first, &server.rs_pk());
        let (our_pk, _our_sk) = box_::gen_keypair();
        let garbage = vec![0xABu8; box_::PUBLICKEYBYTES + box_::MACBYTES];
        let mut bad_seal = RendezvousMessage::new();
        bad_seal.set_key_exchange(KeyExchange {
            keys: vec![our_pk.0.to_vec().into(), garbage.into()],
            version: 1,
            ..Default::default()
        });
        tcp.write_all(&encode_frame(&bad_seal.write_to_bytes().unwrap()))
            .await
            .unwrap();
        let res = timeout(10_000, read_frame(&mut tcp)).await;
        assert!(
            res.is_err() || res.unwrap().is_err(),
            "server must close the connection on an unopenable sealed key"
        );
    })
}
