# nilerr

[![pkg.go.dev][gopkg-badge]][gopkg]

This repository is a fork of the [gostaticanalysis/nilerr](https://github.com/gostaticanalysis/nilerr) repository with additional patches applied.

---

`nilerr` finds code which returns nil even though it checks that error is not nil.

```go
func f() error {
	err := do()
	if err != nil {
		return nil // miss
	}
}
```

`nilerr` also finds code which returns error even though it checks that error is nil.

```go
func f() error {
	err := do()
	if err == nil {
		return err // miss
	}
}
```

`nilerr` ignores code which has a miss with ignore comment.

```go
func f() error {
	err := do()
	if err != nil {
		//lint:ignore nilerr reason
		return nil // ignore
	}
}
```

## How to use
```
$ go install github.com/qawatake/nilerr/cmd/nilerr@latest
$ nilerr ./...
```

<!-- links -->
[gopkg]: https://pkg.go.dev/github.com/qawatake/nilerr
[gopkg-badge]: https://pkg.go.dev/badge/github.com/qawatake/nilerr?status.svg
