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

// An authority that signs the certificates of a test.
type authority struct {
	cert *x509.Certificate
	key  *ecdsa.PrivateKey
	pem  []byte
}

func newAuthority(t *testing.T, name string) *authority {
	t.Helper()
	key, err := ecdsa.GenerateKey(elliptic.P256(), rand.Reader)
	if err != nil {
		t.Fatal(err)
	}
	tmpl := &x509.Certificate{
		SerialNumber:          big.NewInt(1),
		Subject:               pkix.Name{CommonName: name},
		NotBefore:             time.Now().Add(-time.Hour),
		NotAfter:              time.Now().Add(time.Hour),
		IsCA:                  true,
		BasicConstraintsValid: true,
		KeyUsage:              x509.KeyUsageCertSign | x509.KeyUsageDigitalSignature,
	}
	der, err := x509.CreateCertificate(rand.Reader, tmpl, tmpl, &key.PublicKey, key)
	if err != nil {
		t.Fatal(err)
	}
	cert, err := x509.ParseCertificate(der)
	if err != nil {
		t.Fatal(err)
	}
	return &authority{cert, key, pem.EncodeToMemory(&pem.Block{Type: "CERTIFICATE", Bytes: der})}
}

// tlsServer answers every request with "in" over TLS, as the server the
// certificate describes, and gives its port. A nil authority signs the
// certificate with its own key. conf, if given, changes how the server
// speaks TLS; a server that only exchanges keys by RSA has an RSA key.
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
	tmpl.ExtKeyUsage = []x509.ExtKeyUsage{x509.ExtKeyUsageServerAuth}
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
	sc.Certificates = []tls.Certificate{{Certificate: [][]byte{der}, PrivateKey: key}}
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
	animaBin := buildCLI(t, tmp)
	path := filepath.Join(tmp, "tls.anm")
	if err := os.WriteFile(path, []byte(src), 0o644); err != nil {
		t.Fatal(err)
	}
	nativeBin := filepath.Join(tmp, "tls")
	if out, err := exec.Command(animaBin, "build", "-o", nativeBin, path).CombinedOutput(); err != nil {
		t.Fatalf("anima build failed: %v\n%s", err, out)
	}
	roots := filepath.Join(tmp, "roots.pem")
	if err := os.WriteFile(roots, ca.pem, 0o644); err != nil {
		t.Fatal(err)
	}
	// The time of the request is the one part of a message that differs
	// from run to run.
	now := regexp.MustCompile(`current time \S+ is`)
	run := func(backend string, env []string, want string, argv ...string) {
		t.Helper()
		cmd := exec.Command(argv[0], argv[1:]...)
		cmd.Env = append(os.Environ(), env...)
		out, err := cmd.CombinedOutput()
		got := now.ReplaceAllString(string(out), "current time NOW is")
		if err != nil || got != want {
			t.Errorf("%s %v: err=%v, output:\n%s\nwant:\n%s", backend, env, err, got, want)
		}
	}
	for _, zone := range []string{"TZ=UTC", "TZ=Australia/Sydney"} {
		trusted := []string{"SSL_CERT_FILE=" + roots, zone}
		run("VM", trusted, want.String(), animaBin, "run", path)
		run("native", trusted, want.String(), nativeBin)
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
		run("VM", env, untrusted.String(), animaBin, "run", path)
		run("native", env, untrusted.String(), nativeBin)
	}
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
