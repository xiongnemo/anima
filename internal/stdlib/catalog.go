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
		Description:           "TCP listener and stream sockets (listen_tcp, connect_tcp, accept, send_text, recv_text, close)",
		VerificationGuarantee: "Linear Typestate LTS enforcement preventing FD leaks and use-after-close + RAII ? unwind cleanup",
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
		Description:           "Safe binary protocol cursor ByteView (from_str, from_hex, len, read_u8, read_u16_be, read_u32_be, slice)",
		VerificationGuarantee: "AoRTE static bounds proofs via AnimaSMT eliminating out-of-bounds buffer reads",
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
