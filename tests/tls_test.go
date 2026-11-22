package tests

import (
	"crypto"
	"crypto/ecdsa"
	"crypto/elliptic"
	"crypto/rand"
	"crypto/rsa"
	"crypto/tls"
	"crypto/x509"
	"crypto/x509/pkix"
	"encoding/pem"
	"io"
	"log"
	"math/big"
	"net"
	"net/http"
	"os"
	"os/exec"
	"path/filepath"
	"regexp"
	"strconv"
	"strings"
	"testing"
	"time"
)

// An authority that signs the certificates of a test. A server with a
// certificate of it sends "sends" after its own: the authorities between
// the certificate and the first one.
type authority struct {
	cert  *x509.Certificate
	key   *ecdsa.PrivateKey
	pem   []byte
	sends [][]byte
}

func newAuthority(t *testing.T, name string) *authority {
	t.Helper()
	return signedAuthority(t, nil, &x509.Certificate{Subject: pkix.Name{CommonName: name}})
}

// signedAuthority is an authority that parent stands for; a nil parent
// leaves it to stand for itself.
func signedAuthority(t *testing.T, parent *authority, tmpl *x509.Certificate) *authority {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	tmpl.SerialNumber = big.NewInt(1)
	// One that says it is no authority is left to say so.
	if !tmpl.BasicConstraintsValid {
		tmpl.IsCA, tmpl.BasicConstraintsValid = true, true
	}
	tmpl.KeyUsage = x509.KeyUsageCertSign | x509.KeyUsageDigitalSignature
	if tmpl.NotAfter.IsZero() {
		tmpl.NotBefore = time.Now().Add(-time.Hour)
		tmpl.NotAfter = time.Now().Add(time.Hour)
	}
	by, signer := tmpl, key
	var sends [][]byte
	if parent != nil {
		by, signer = parent.cert, parent.key
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, by, &key.PublicKey, signer)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatal(err)
	}
	if parent != nil {
		sends = append([][]byte{der}, parent.sends...)
	}
	return &authority{cert, key, pemOf(der), sends}
}

func pemOf(der []byte) []byte {
	return pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der})
}

// tlsServer answers every request with "in" over TLS, as the server the
// certificate describes, and gives its port. A nil authority signs the
// certificate with its own key, and the certificate is left in tmpl.Raw.
// conf, if given, changes how the server speaks TLS; a server that only
// exchanges keys by RSA has an RSA key.
func tlsServer(t *testing.T, ca *authority, tmpl *x509.Certificate, conf func(*tls.Config)) string {
	t.Helper()
	sc := &tls.Config{}
	if conf != nil {
		conf(sc)
	}
	var key crypto.Signer
	var err error
	if len(sc.CipherSuites) > 0 {
		key, err = rsa.GenerateKey(rand.Reader, 2048)
		tmpl.KeyUsage = x509.KeyUsageKeyEncipherment
	} else {
		key, err = ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	}
	if err != nil {
		t.Fatal(err)
	}
	tmpl.SerialNumber = big.NewInt(2)
	tmpl.KeyUsage |= x509.KeyUsageDigitalSignature
	if tmpl.ExtKeyUsage == nil {
		tmpl.ExtKeyUsage = []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth}
	}
	if tmpl.NotAfter.IsZero() {
		tmpl.NotBefore = time.Now().Add(-time.Hour)
		tmpl.NotAfter = time.Now().Add(time.Hour)
	}
	parent, signer := tmpl, key
	if ca != nil {
		parent, signer = ca.cert, ca.key
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, parent, key.Public(), signer)
	if err != nil {
		t.Fatal(err)
	}
	tmpl.Raw = der
	chain := [][]byte{der}
	if ca != nil {
		chain = append(chain, ca.sends...)
	}
	sc.Certificates = []tls.Certificate{{Certificate: chain, PrivateKey: key}}
	ln, err := tls.Listen("tcp", "127.0.0.1:0", sc)
	if err != nil {
		t.Fatal(err)
	}
	srv := &http.Server{
		Handler:  http.HandlerFunc(func(w http.ResponseWriter, _ *http.Request) { _, _ = io.WriteString(w, "in") }),
		ErrorLog: log.New(io.Discard, "", 0),
	}
	go func() { _ = srv.Serve(ln) }()
	t.Cleanup(func() { srv.Close() })
	_, port, _ := net.SplitHostPort(ln.Addr().String())
	return port
}

// An HTTPS server is who the URL says only if its certificate says so and
// an authority of the system stands for it. The native client checked
// neither: it gave the answer of any server that could do a handshake,
// where the VM gave an Err. Both refuse now, for the reason Go gives.
func TestE2ETLSCertificateIsVerified(t *testing.T) {
	ca, other := newAuthority(t, "anima test authority"), newAuthority(t, "another authority")
	local := []net.IP{net.ParseIP("127.0.0.1")}
	servers := []struct {
		name string
		ca   *authority
		cert x509.Certificate
		want string
	}{
		{"good", ca, x509.Certificate{IPAddresses: local}, "200 in"},
		{"good-with-names", ca, x509.Certificate{IPAddresses: local, DNSNames: []string{"a.test", "*.b.test"}}, "200 in"},
		{"other-authority", other, x509.Certificate{IPAddresses: local},
			"x509: certificate signed by unknown authority"},
		{"self-signed", nil, x509.Certificate{IPAddresses: local},
			"x509: certificate signed by unknown authority"},
		{"other-address", ca, x509.Certificate{IPAddresses: []net.IP{net.ParseIP("10.1.2.3"), net.ParseIP("::1"), net.ParseIP("2001:db8::7")}},
			"x509: certificate is valid for 10.1.2.3, ::1, 2001:db8::7, not 127.0.0.1"},
		{"names-only", ca, x509.Certificate{DNSNames: []string{"a.test", "*.b.test"}},
			"x509: cannot validate certificate for 127.0.0.1 because it doesn't contain any IP SANs"},
		{"common-name", ca, x509.Certificate{Subject: pkix.Name{CommonName: "127.0.0.1"}},
			"x509: certificate relies on legacy Common Name field, use SANs instead"},
		{"other-common-name", ca, x509.Certificate{Subject: pkix.Name{CommonName: "a.test"}},
			"x509: cannot validate certificate for 127.0.0.1 because it doesn't contain any IP SANs"},
		{"expired", ca, x509.Certificate{IPAddresses: local,
			NotBefore: time.Date(2001, 1, 2, 3, 4, 5, 0, time.UTC), NotAfter: time.Date(2002, 1, 2, 3, 4, 5, 0, time.UTC)},
			"x509: certificate has expired or is not yet valid: current time NOW is after 2002-01-02T03:04:05Z"},
		{"not-yet", ca, x509.Certificate{IPAddresses: local,
			NotBefore: time.Date(2901, 1, 2, 3, 4, 5, 0, time.UTC), NotAfter: time.Date(2902, 1, 2, 3, 4, 5, 0, time.UTC)},
			"x509: certificate has expired or is not yet valid: current time NOW is before 2901-01-02T03:04:05Z"},
		// More than one thing wrong: the dates, then the names, then the authority.
		{"self-signed-other-address", nil, x509.Certificate{IPAddresses: []net.IP{net.ParseIP("10.1.2.3")}},
			"x509: certificate is valid for 10.1.2.3, not 127.0.0.1"},
		{"all-wrong", nil, x509.Certificate{DNSNames: []string{"a.test"},
			NotBefore: time.Date(2001, 1, 2, 3, 4, 5, 0, time.UTC), NotAfter: time.Date(2002, 1, 2, 3, 4, 5, 0, time.UTC)},
			"x509: certificate has expired or is not yet valid: current time NOW is after 2002-01-02T03:04:05Z"},
	}
	var calls, want, untrusted strings.Builder
	for i := range servers {
		s := &servers[i]
		port := tlsServer(t, s.ca, &s.cert, nil)
		calls.WriteString(`    get("` + s.name + `", "https://127.0.0.1:` + port + `/")` + "\n")
		line := s.name + " " + s.want
		if strings.HasPrefix(s.want, "x509") {
			line = s.name + ` ERR Get "https://127.0.0.1:` + port + `/": tls: failed to verify certificate: ` + s.want
		}
		want.WriteString(line + "\n")
		// With no authority of the test known, none of them is the server.
		why := "x509: certificate signed by unknown authority"
		if s.ca == ca && strings.HasPrefix(s.want, "x509") || strings.Contains(s.name, "wrong") || strings.Contains(s.name, "other-address") {
			why = s.want
		}
		untrusted.WriteString(s.name + ` ERR Get "https://127.0.0.1:` + port + `/": tls: failed to verify certificate: ` + why + "\n")
	}
	src := `import std.requests as req

def get(name: str, url: str) -> int:
    match req.get(url, timeout_ms=5000):
        Ok(r) -> print(name, r.status, r.body)
        Err(m) -> print(name, "ERR", m)
    return 0

def main() -> int:
` + calls.String() + `    return 0
`
	tmp := t.TempDir()
	run := tlsBackends(t, "tls", src)
	roots := filepath.Join(tmp, "roots.pem")
	if err := os.WriteFile(roots, ca.pem, 0o644); err != nil {
		t.Fatal(err)
	}
	for _, zone := range []string{"TZ=UTC", "TZ=Australia/Sydney"} {
		trusted := []string{"SSL_CERT_FILE=" + roots, zone}
		run(trusted, want.String())
	}
	// An empty file of authorities holds none; the system's own do not
	// know the test's either.
	none := filepath.Join(tmp, "none")
	if err := os.Mkdir(none, 0o755); err != nil {
		t.Fatal(err)
	}
	empty := filepath.Join(none, "empty.pem")
	if err := os.WriteFile(empty, nil, 0o644); err != nil {
		t.Fatal(err)
	}
	for _, env := range [][]string{nil, {"SSL_CERT_FILE=" + empty, "SSL_CERT_DIR=" + none}} {
		run(env, untrusted.String())
	}
}

// tlsBackends builds src for both backends and gives a function that runs
// both with env added to the environment and wants the same output of
// each. The time of the request is the one part of a message that differs
// from run to run: it is written NOW in want.
func tlsBackends(t *testing.T, name, src string) func(env []string, want string) {
	t.Helper()
	tmp := t.TempDir()
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, name+".anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	nativeBin := filepath.Join(tmp, name)
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	now := regexp.MustCompile(`current time \S+ is`)
	// Only the VM goes on to say why an authority is not known.
	hint := regexp.MustCompile(` \(possibly because of ".*" while trying to verify candidate authority certificate "[^"]*"\)`)
	return func(env []string, want string) {
		t.Helper()
		for _, argv := range [][]string{{animaBin, "run", path}, {nativeBin}} {
			cmd := exec.Command(argv[0], argv[1:]...)
			cmd.Env = append(os.Environ(), env...)
			out, err := cmd.CombinedOutput()
			got := now.ReplaceAllString(string(out), "current time NOW is")
			got = hint.ReplaceAllString(got, "")
			if err != nil || got != want {
				t.Errorf("%v %v: err=%v, output:\n%s\nwant:\n%s", argv[1:], env, err, got, want)
			}
		}
	}
}

// An authority is one the system's authorities stand for, through others
// the server sends; and whatever is among the system's authorities stands
// for itself and for what it signed, whether it is the first of its line
// or not. The native client took only one that signed itself, so a server
// under an authority trusted in the middle of its line was refused. One
// that is not what it has to be is refused in the VM's words.
func TestE2ETLSLineOfAuthorities(t *testing.T) {
	local := []net.IP{net.ParseIP("127.0.0.1")}
	old := func() (time.Time, time.Time) {
		return time.Date(2001, 1, 2, 3, 4, 5, 0, time.UTC), time.Date(2002, 1, 2, 3, 4, 5, 0, time.UTC)
	}
	// first is among the system's authorities; of the other lines only
	// the one named is.
	first := newAuthority(t, "first")
	second := signedAuthority(t, first, &x509.Certificate{Subject: pkix.Name{CommonName: "second"}})
	third := signedAuthority(t, second, &x509.Certificate{Subject: pkix.Name{CommonName: "third"}})
	silent := *second
	silent.sends = nil
	late := &x509.Certificate{Subject: pkix.Name{CommonName: "late"}}
	late.NotBefore, late.NotAfter = old()
	narrow := signedAuthority(t, first, &x509.Certificate{Subject: pkix.Name{CommonName: "narrow"}, MaxPathLenZero: true})
	// One with second's name and another key, sent in second's place.
	other := signedAuthority(t, first, &x509.Certificate{Subject: pkix.Name{CommonName: "second"}})
	swapped := *second
	swapped.sends = other.sends
	leaf := signedAuthority(t, first, &x509.Certificate{Subject: pkix.Name{CommonName: "leaf"}, BasicConstraintsValid: true})
	unknown := newAuthority(t, "unknown")
	middle := signedAuthority(t, unknown, &x509.Certificate{Subject: pkix.Name{CommonName: "middle"}})
	lateFirst := &x509.Certificate{Subject: pkix.Name{CommonName: "late first"}}
	lateFirst.NotBefore, lateFirst.NotAfter = old()
	own := x509.Certificate{Subject: pkix.Name{CommonName: "own"}, IPAddresses: local}
	servers := []struct {
		name string
		ca   *authority
		cert *x509.Certificate
		want string
	}{
		{"second", second, &x509.Certificate{IPAddresses: local}, "200 in"},
		{"third", third, &x509.Certificate{IPAddresses: local}, "200 in"},
		{"second-not-sent", &silent, &x509.Certificate{IPAddresses: local},
			"x509: certificate signed by unknown authority"},
		{"second-with-another-key", &swapped, &x509.Certificate{IPAddresses: local},
			"x509: certificate signed by unknown authority"},
		{"no-authority", leaf, &x509.Certificate{IPAddresses: local},
			"x509: certificate signed by unknown authority"},
		{"late-authority", signedAuthority(t, first, late), &x509.Certificate{IPAddresses: local},
			"x509: certificate has expired or is not yet valid: current time NOW is after 2002-01-02T03:04:05Z"},
		{"late-first-authority", signedAuthority(t, nil, lateFirst), &x509.Certificate{IPAddresses: local},
			"x509: certificate has expired or is not yet valid: current time NOW is after 2002-01-02T03:04:05Z"},
		{"one-too-many", signedAuthority(t, narrow, &x509.Certificate{Subject: pkix.Name{CommonName: "below"}}), &x509.Certificate{IPAddresses: local},
			"x509: too many intermediates for path length constraint"},
		{"for-a-client", first, &x509.Certificate{IPAddresses: local, ExtKeyUsage: []x509.ExtKeyUsage{x509.ExtKeyUsageClientAuth}},
			"x509: certificate specifies an incompatible key usage"},
		{"middle-trusted", middle, &x509.Certificate{IPAddresses: local}, "200 in"},
		{"itself-trusted", unknown, &own, "200 in"},
		{"itself-trusted-other-address", unknown, &x509.Certificate{IPAddresses: []net.IP{net.ParseIP("10.1.2.3")}},
			"x509: certificate is valid for 10.1.2.3, not 127.0.0.1"},
	}
	var calls, want strings.Builder
	roots := append(append([]byte{}, first.pem...), middle.pem...)
	for _, s := range servers {
		port := tlsServer(t, s.ca, s.cert, nil)
		if strings.HasPrefix(s.name, "itself-trusted") {
			roots = append(roots, pemOf(s.cert.Raw)...)
		}
		if s.name == "late-first-authority" {
			roots = append(roots, s.ca.pem...)
		}
		calls.WriteString(`    get("` + s.name + `", "https://127.0.0.1:` + port + `/")` + "\n")
		line := s.name + " " + s.want
		if strings.HasPrefix(s.want, "x509") {
			line = s.name + ` ERR Get "https://127.0.0.1:` + port + `/": tls: failed to verify certificate: ` + s.want
		}
		want.WriteString(line + "\n")
	}
	file := filepath.Join(t.TempDir(), "roots.pem")
	if err := os.WriteFile(file, roots, 0o644); err != nil {
		t.Fatal(err)
	}
	tlsBackends(t, "tls_line", `import std.requests as req

def get(name: str, url: str) -> int:
    match req.get(url, timeout_ms=5000):
        Ok(r) -> print(name, r.status, r.body)
        Err(m) -> print(name, "ERR", m)
    return 0

def main() -> int:
`+calls.String()+`    return 0
`)([]string{"SSL_CERT_FILE=" + file}, want.String())
}

// The native client speaks TLS as the VM does: 1.2 or later, and with a
// key agreed on anew for each connection. It took a server that only
// exchanges keys by RSA, which Go does not; neither takes TLS 1.1, or a
// server that does not speak TLS at all.
func TestE2ETLSHandshakeParity(t *testing.T) {
	ca := newAuthority(t, "anima test authority")
	local := []net.IP{net.ParseIP("127.0.0.1")}
	servers := []struct {
		name string
		conf func(*tls.Config)
		want string
	}{
		{"tls-1.3", func(c *tls.Config) { c.MinVersion = tls.VersionTLS13 }, "200 in"},
		{"tls-1.2", func(c *tls.Config) { c.MaxVersion = tls.VersionTLS12 }, "200 in"},
		{"tls-1.1", func(c *tls.Config) { c.MinVersion, c.MaxVersion = tls.VersionTLS10, tls.VersionTLS11 }, "refused"},
		{"rsa-exchange", func(c *tls.Config) {
			c.MaxVersion = tls.VersionTLS12
			c.CipherSuites = []uint16{tls.TLS_RSA_WITH_AES_128_GCM_SHA256, tls.TLS_RSA_WITH_AES_256_CBC_SHA}
		}, "refused"},
		{"ecdhe-rsa", func(c *tls.Config) {
			c.MaxVersion = tls.VersionTLS12
			c.CipherSuites = []uint16{tls.TLS_ECDHE_RSA_WITH_AES_128_GCM_SHA256}
		}, "200 in"},
		{"ecdhe-rsa-cbc", func(c *tls.Config) {
			c.MaxVersion = tls.VersionTLS12
			c.CipherSuites = []uint16{tls.TLS_ECDHE_RSA_WITH_AES_256_CBC_SHA}
		}, "200 in"},
	}
	var calls, want strings.Builder
	for _, s := range servers {
		port := tlsServer(t, ca, &x509.Certificate{IPAddresses: local}, s.conf)
		calls.WriteString(`    get("` + s.name + `", "https://127.0.0.1:` + port + `/")` + "\n")
		want.WriteString(s.name + " " + s.want + "\n")
	}
	// A server that says HTTP to whatever it hears.
	ln, err := net.Listen("tcp", "127.0.0.1:0")
	if err != nil {
		t.Fatal(err)
	}
	t.Cleanup(func() { ln.Close() })
	go func() {
		for {
			c, err := ln.Accept()
			if err != nil {
				return
			}
			_, _ = io.WriteString(c, "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nin")
			c.Close()
		}
	}()
	_, plain, _ := net.SplitHostPort(ln.Addr().String())
	calls.WriteString(`    get("no-tls", "https://127.0.0.1:` + plain + `/")` + "\n")
	want.WriteString("no-tls refused\n")
	roots := filepath.Join(t.TempDir(), "roots.pem")
	if err := os.WriteFile(roots, ca.pem, 0o644); err != nil {
		t.Fatal(err)
	}
	t.Setenv("SSL_CERT_FILE", roots)
	// What went wrong in a handshake is told in other words by each backend.
	runOnBothBackends(t, "tls_handshake", `import std.requests as req

def get(name: str, url: str) -> int:
    match req.get(url, timeout_ms=5000):
        Ok(r) -> print(name, r.status, r.body)
        Err(m) -> print(name, "refused")
    return 0

def main() -> int:
`+calls.String()+`    return 0
`, want.String())
}

// Requests made at the same time each hear what was wrong with their own
// server's certificate, not another's.
func TestE2ETLSAtTheSameTime(t *testing.T) {
	ca := newAuthority(t, "anima test authority")
	local := []net.IP{net.ParseIP("127.0.0.1")}
	good := tlsServer(t, ca, &x509.Certificate{IPAddresses: local}, nil)
	names := tlsServer(t, ca, &x509.Certificate{DNSNames: []string{"a.test"}}, nil)
	self := tlsServer(t, nil, &x509.Certificate{IPAddresses: local}, nil)
	roots := filepath.Join(t.TempDir(), "roots.pem")
	if err := os.WriteFile(roots, ca.pem, 0o644); err != nil {
		t.Fatal(err)
	}
	t.Setenv("SSL_CERT_FILE", roots)
	url := func(port string) string { return "https://127.0.0.1:" + port + "/" }
	var calls strings.Builder
	var fs []string
	for i := 0; i < 8; i++ {
		for _, port := range []string{good, names, self} {
			f := "f" + strconv.Itoa(len(fs))
			fs = append(fs, f)
			calls.WriteString("    " + f + ` = sess.get_async("` + url(port) + `", timeout_ms=5000)` + "\n")
		}
	}
	src := `import std.requests as req

def main() -> int:
    sess = req.Session(8)
` + calls.String() + `    resps = req.gather([` + strings.Join(fs, ", ") + `])
    sess.close()
    for r in resps:
        match r:
            Ok(resp) -> print(resp.status, resp.body)
            Err(e) -> print(e)
    return 0
`
	one := "200 in\n" +
		`Get "` + url(names) + `": tls: failed to verify certificate: x509: cannot validate certificate for 127.0.0.1 because it doesn't contain any IP SANs` + "\n" +
		`Get "` + url(self) + `": tls: failed to verify certificate: x509: certificate signed by unknown authority` + "\n"
	runOnBothBackends(t, "tls_together", src, strings.Repeat(one, 8))
}
