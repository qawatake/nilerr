package a

import "errors"

func f() (err error) {
	defer wrap(&err)
	err = do()
	if err != nil {
		return nil // want "error is not nil"
	}
	return errors.New("hoge")
}

func do() error { return nil }

func wrap(errp *error) {}
