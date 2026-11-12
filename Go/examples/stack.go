package stack

import "errors"

// Stack is a generic stack with a fixed capacity.
type Stack[T any] struct {
	items []T
	limit int
}

var ErrFull = errors.New("stack is full")
var ErrEmpty = errors.New("stack is empty")

// New creates an empty stack that holds at most limit elements.
func New[T any](limit int) *Stack[T] {
	return &Stack[T]{limit: limit}
}

func (s *Stack[T]) Push(x T) error {
	if len(s.items) >= s.limit {
		return ErrFull
	}
	s.items = append(s.items, x)
	return nil
}

func (s *Stack[T]) Pop() (T, error) {
	var zero T
	n := len(s.items)
	if n == 0 {
		return zero, ErrEmpty
	}
	x := s.items[n-1]
	s.items = s.items[:n-1]
	return x, nil
}

// Map applies f to every element of xs.
func Map[T, U any](xs []T, f func(T) U) []U {
	ys := make([]U, 0, len(xs))
	for _, x := range xs {
		ys = append(ys, f(x))
	}
	return ys
}

type Number interface {
	~int | ~int64 | ~float64
}

func Sum[N Number](xs ...N) (total N) {
	for _, x := range xs {
		total += x
	}
	return
}
