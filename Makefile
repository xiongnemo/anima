.PHONY: build test vet clean

build:
	CGO_ENABLED=0 go build -o anima ./cmd/anima

vet:
	go vet ./...

test: vet
	go test -v -race -short ./...
	go test -v ./internal/verify/smt

clean:
	rm -f anima *.anbc
