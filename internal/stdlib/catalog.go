package stdlib

// ModuleSpec describes each of the 8 formally-verified standard library modules.
type ModuleSpec struct {
	Path                  string
	Description           string
	VerificationGuarantee string
}

var Modules = []ModuleSpec{
	{
		Path:                  "std.fp",
		Description:           "Total-terminating higher-order combinators (map, filter, fold, sum, zip, take, drop, find, any, all, flat_map, filter_ok, unwrap_or, and_then)",
		VerificationGuarantee: "Guaranteed termination without decreases clauses + linear length/sum bound propagation in AnimaSMT",
	},
	{
		Path:                  "std.concurrent",
		Description:           "Bounded ThreadPool, Channel, Mutex, Semaphore, and parallel_map",
		VerificationGuarantee: "Petri Net pool conservation + shutdown leak detection + deadlock/starvation checks",
	},
	{
		Path:                  "std.socket",
		Description:           "TCP listener and stream sockets (listen_tcp, connect_tcp, accept, send_text, recv_text, close) and UDP sockets (bind_udp, send_to, recv_from, close)",
		VerificationGuarantee: "Ownership and typestate checking: every socket has one owner that closes it on every path; no use after close or move, no sharing of a stream or a UDP socket between threads; ports, receive sizes and waits proved in range",
	},
	{
		Path:                  "std.requests",
		Description:           "Synchronous & async pooled HTTP/HTTPS client (get, post, Session, get_async, gather)",
		VerificationGuarantee: "Mandatory bounded timeout_ms: int[1..300_000] liveness contract + Petri Future consumption checks",
	},
	{
		Path:                  "std.json",
		Description:           "Schema-verified JSON encode/decode[EntityType]",
		VerificationGuarantee: "Runtime boundary sanitization enforcing every refinement int[lo..hi] range and SPARK entity invariant",
	},
	{
		Path:                  "std.bytes",
		Description:           "Immutable byte views for binary protocols: read (len, read_u8, read_u16_be, read_u32_be, slice) and build (from_str, from_hex, u8, u16_be, u32_be, random, concat, to_hex)",
		VerificationGuarantee: "AoRTE static bounds proofs via AnimaSMT eliminating out-of-bounds buffer reads; the length of every view that is built is known, and every number written is proved to fit its bytes",
	},
	{
		Path:                  "std.crypto",
		Description:           "Cryptographic hashing & constant-time MAC verification (sha256, hmac_sha256, constant_time_eq)",
		VerificationGuarantee: "Side-channel constant-time equality & OpenSSL 3.0 native parity",
	},
	{
		Path:                  "std.fs",
		Description:           "File I/O (open, read_text, write_atomic), std.cli (args, env_get), and std.time (now_ms, sleep_ms)",
		VerificationGuarantee: "Linear File Typestate close checks + atomic temp-rename writes",
	},
}
