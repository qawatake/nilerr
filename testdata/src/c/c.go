package c

import "context"

func fff(ctx context.Context) (err error) {
	defer wrap(&err)
	err = do()
	if err != nil {
		log(ctx, err)
		return nil // ok
	}
	return nil
}

func do() error { return nil }

func wrap(errp *error) {}

func log(ctx context.Context, err error) {}
