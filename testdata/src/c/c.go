package c

func j() (interface{}, error) {
	if err := do(); err != nil {
		return nil, nil // want "error is not nil"
	}

	if err := do(); err != nil {
		return nil, err
	}
	return nil, nil
}

func do() error {
	return nil
}
