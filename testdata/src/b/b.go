package a

import (
	"context"
	"errors"
	"log"
	"testing"
)

func f() (err error) {
	defer wrap(&err)
	err = do()
	if err != nil {
		return nil // want "error is not nil"
	}

	err = do()
	if err != nil {
		return nil // want "error is not nil"
	}

	err = do()
	if err != nil {
		//lint:ignore nilerr reason
		return nil // OK
	}

	err = do()
	if err == nil || checkErr(err) {
		return err
	}

	return nil
}

func g() (err error) {
	defer wrap(&err)
	err = do()
	if err == nil {
		return err // want "error is nil"
	}

	err = do()
	if err == nil {
		return err // want "error is nil"
	}

	bytes, err := do2()
	if err == nil {
		_ = bytes
		return err // want "error is nil"
	}

	err = do()
	if err == nil {
		return errors.New("another error") // OK
	}

	err = do()
	if err != nil {
		return errors.New(err.Error()) // OK, error is wrapped
	}

	err = do()
	if err != nil {
		CustomLoggingFunc(err) // OK
		return nil
	}

	err = do()
	if err != nil {
		Logf(context.Background(), "error: %+v", err) // OK
		return nil
	}

	err = do()
	if err != nil {
		Logf(context.Background(), "error: %s", err.Error()) // OK
		return nil
	}

	err = do()
	if err != nil {
		LogTypedf(context.Background(), "error: %+v", err) // OK
		return nil
	}

	err = do()
	if err != nil {
		LogSinglef(context.Background(), "error: %+v", err) // OK
		return nil
	}

	err = do()
	if err != nil {
		NewLogger().CustomLoggingFunc(err) // OK
		return nil
	}

	err = do()
	if err != nil {
		//lint:ignore nilerr reason
		return nil // OK
	}

	return nil
}

func h() {
	f0 := func() error {
		for {
			if err := do(); err != nil {
				break
			}
		}
		return nil // want "error is not nil"
	}
	_ = f0

	f1 := func(t *testing.T) error {
		for {
			if err := do(); err != nil {
				t.Fatal(err)
			}
		}
		return nil
	}
	_ = f1
}

func i() (err1 error, err2 error) {
	defer wrap(&err1)
	defer wrap(&err2)
	err1 = do()
	if err1 != nil {
		return nil, nil // want "error is not nil"
	}

	err1 = do()
	if err1 != nil {
		return nil, err1
	}

	err1 = do()
	if err1 != nil {
		return err1, nil
	}

	err1 = do()
	if err1 != nil {
		return err1, err1
	}

	return nil, nil
}

func j() (_ interface{}, err error) {
	defer wrap(&err)
	err = do()
	if err != nil {
		return nil, nil // want "error is not nil"
	}

	err = do()
	if err != nil {
		return nil, err
	}

	err = do()
	if err != nil {
		return err, nil // want "error is not nil"
	}

	err = do()
	if err != nil {
		return err, err
	}

	return nil, nil
}

func k() {
	if err := do(); err != nil {
		return
	}

	if err := do(); err == nil {
		return
	}
}

func l() (err error) {
	defer wrap(&err)
	var e = errors.New("x")

	bytes, err := do2()
	if err != nil {
		return err
	}
	defer func() error { return nil }()

	for {
		var buf []byte
		buf, err = do2()
		if err == e {
			for err == e {
				_, err = do2()
			}
			if err != nil {
				err = errors.New("a")
				break
			}
		}
		_ = buf
	}

	_ = bytes
	return nil // want "error is not nil"
}

func do() error {
	return nil
}

func do2() ([]byte, error) {
	return nil, nil
}

func checkErr(err error) bool {
	return true
}

func CustomLoggingFunc(err error) {
	log.Printf("%+v", err)
}

func Logf(ctx context.Context, msg string, args ...interface{}) {
	log.Printf(msg, args...)
}

func LogTypedf(ctx context.Context, msg string, args ...error) {
	log.Printf(msg, args[0])
}

func LogSinglef(ctx context.Context, msg string, arg interface{}) {
	log.Printf(msg, arg)
}

type logger int

func NewLogger() *logger {
	l := logger(0)
	return &l
}

func (l *logger) CustomLoggingFunc(err error) {
	log.Printf("%+v", err)
}

func wrap(errp *error) {}
