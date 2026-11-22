# STUN NAT detection (`examples/stun.anm`)

The example asks a STUN server what the NAT in front of a host does to its UDP. It is a client, a server to try the client against, and the two run against each other in 15 simulated NATs. IPv4 only.

```
anima run examples/stun.anm                                      # the 15 scenes
anima run examples/stun.anm -- client stun.example.org           # port 3478 unless another is given
anima run examples/stun.anm -- server 192.0.2.1 192.0.2.2        # ports 3478 and 3479 unless two are given
```

The client prints the mapped address, the mapping and filtering behaviour of RFC 5780, and the class of RFC 3489:

```
mapped address: 203.0.113.7:40000
mapping:        endpoint-independent
filtering:      address and port-dependent
RFC 3489:       port restricted cone NAT
```

It exits 0 when it was answered, 1 when it was not or a socket failed, 2 on arguments it cannot read.

## What the client asks

Each request is a Binding request with the magic cookie and 96 random bits. It is sent three times at most, waiting 500 ms, 1 s and 2 s (50, 100 and 200 ms in the scenes). A datagram is the answer when it is a Binding response or error of that transaction and every attribute ends inside it; anything else heard meanwhile is passed over, 64 datagrams at most for each sending.

| Step | Request | What it tells |
|---|---|---|
| `binding` | to the server | the mapped address, and the server's other address and port (`OTHER-ADDRESS`, or `CHANGED-ADDRESS` of an RFC 3489 server) |
| `change_both` | to the server, `CHANGE-REQUEST` of address and port | answered from the other address and port: filtering is endpoint-independent |
| `change_port` | to the server, `CHANGE-REQUEST` of port | answered: address-dependent. Not answered: address and port-dependent |
| `other_address` | to the other address, same port | the same mapped address: mapping is endpoint-independent |
| `other_port` | to the other address, other port | the same as the one before: address-dependent. Another: address and port-dependent |

The mapping is `none` when the mapped address has the socket's port and is an address of this host (a socket can be bound at it); the two mapping steps are then not taken.

The filtering steps come first, and `property FilterFirst` holds the workflow to it: a request to the server's other address opens an address-dependent filter to that address, and a filtering step after it would find the filter open. RFC 5780 makes the filtering tests from a second socket for the same reason; one socket and this order need no second mapping.

What is not found is `not told`, never a guess:

- a server that names no other address, or one that differs from its own in the address only or the port only: mapping and filtering are both `not told` (mapping `none` is still found);
- a `CHANGE-REQUEST` answered with an error, or from an end that was not asked for: filtering is `not told`;
- no answer to the request sent to the other address, or one without a mapped address: mapping is `not told`. Where that answer came from is not looked at: its mapped address is what the server saw of a request sent to that address, whichever of its ends answers.

The RFC 3489 class is read off the two:

| Mapping | Filtering | Class |
|---|---|---|
| none | endpoint-independent | open internet |
| none | address-dependent, or address and port-dependent | symmetric UDP firewall |
| endpoint-independent | endpoint-independent | full cone NAT |
| endpoint-independent | address-dependent | restricted cone NAT |
| endpoint-independent | address and port-dependent | port restricted cone NAT |
| address-dependent, or address and port-dependent | any, or not told | symmetric NAT |
| not told | any | not told |
| none or endpoint-independent | not told | not told |

No answer to the first request is `UDP blocked`.

## The server

`stun server IP IP2 [PORT PORT2]` binds four sockets, the two ports at each address, and serves until it is killed. It answers a Binding request from the end the `CHANGE-REQUEST` asks for, with `XOR-MAPPED-ADDRESS`, `MAPPED-ADDRESS`, `RESPONSE-ORIGIN` and `OTHER-ADDRESS`. A request without the magic cookie is answered as RFC 3489 has it: `MAPPED-ADDRESS`, `SOURCE-ADDRESS`, `CHANGED-ADDRESS`. A request with a comprehension-required attribute it does not know is answered with error 420 and `UNKNOWN-ATTRIBUTES`. A datagram that is no Binding request, or whose attributes do not end where it does, is not answered. Neither backend reads more than 1500 bytes of a datagram, so a longer one is answered only if its first 1500 bytes are a whole request.

It has no `FINGERPRINT`, no `MESSAGE-INTEGRITY`, no `RESPONSE-PORT` and no `PADDING`, and it listens on UDP only.

It is a server to try the client against, not one to leave on the internet:

- **It answers whoever asks, as often as asked.** An answer is some three times its request and goes to the address the request says it came from, from another address of the server when the request asks so. RFC 5780 recommends a limit on how often; this server has none.
- **Run natively it grows until it is killed.** The native backend gives no value back before the program ends ([backends.md](backends.md)): measured, about 60 kB a second with nothing to hear (it looks at each socket every 5 ms) and about 20 kB a request. On the VM it does not grow. The scenes and the client end, and are not touched by this.
- **It hears its four sockets in turn**, 5 ms each, so a request waits 15 ms at most and one socket answers some 70 requests a second.

In the scenes the server stands on `127.0.0.1` and `127.0.0.2` and plays the NAT as well: a `Scene` says which mapped address it reports for each of its ends, which of its ends may answer given the ends the client has sent to, and which kind of server it is (RFC 5780, RFC 3489, one that names no other address, one that refuses `CHANGE-REQUEST`).

## What is proved

- **Every read is inside the datagram.** `answer` and `request_of` walk the attributes with a view that gets shorter; each `read_u16_be`, each `slice` and the `ERROR-CODE` and `CHANGE-REQUEST` values are proved inside what is left. The address a datagram came from is read as four bytes only where it is known to be four. See [contracts.md](contracts.md#byte-views).
- **Every number fits its field.** A port is `int[1..65535]`, an address `int[0..4294967295]`, a message length is proved to be at most 65535 where the header is written, an error code is in `0..799`.
- **Both walks end.** Each has `decreases: rest.len()`; the retry loop and the wait for an answer count down.
- **A socket is closed on every path.** The client's one and the server's four are closed by hand where a later `bind_udp` fails; `?` is not written while one is held. See [ownership.md](ownership.md).
- **`workflow Discover` is a sound, 1-safe net**, and `system Discovery` satisfies `FilterFirst`.

`tests/stun_test.go` takes thirteen of these checks out of the example one at a time and expects each to be refused at that place.

## What is not proved

- That the verdict is the right one for a NAT: the table above is the program, not a theorem. The tests are the 15 scenes, a Go copy of the reader compared on changed messages on both backends, and the server asked over real sockets.
- Anything about time: an answer that comes after the last wait is no answer, and a NAT that is slow looks like one that filters.
- Hairpinning, the lifetime of a mapping, and IPv6 are not looked at.

Two things the contract kernel does not know made the reader longer than it would be: the range of `x % 4` is not known, and `x / 4 * 4` is bounded only where `x` has a range type. The reader pads a length with `(size + 3) / 4 * 4` on a `read_u16_be`, which has one.
