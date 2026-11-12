package shapes

import (
	"fmt"
	"math"
)

type Shape interface {
	Area() float64
	Perimeter() float64
}

type Circle struct{ R float64 }

type Rect struct {
	W, H float64
}

func (c Circle) Area() float64      { return math.Pi * c.R * c.R }
func (c Circle) Perimeter() float64 { return 2 * math.Pi * c.R }
func (r Rect) Area() float64        { return r.W * r.H }
func (r Rect) Perimeter() float64   { return 2 * (r.W + r.H) }

// Describe prints what it knows about a shape.
func Describe(s Shape) string {
	switch v := s.(type) {
	case Circle:
		return fmt.Sprintf("circle of radius %g", v.R)
	case Rect:
		if v.W == v.H {
			return fmt.Sprintf("square of side %g", v.W)
		}
		return fmt.Sprintf("rectangle %g x %g", v.W, v.H)
	default:
		return "unknown shape"
	}
}

func Largest(shapes []Shape) (best Shape) {
	for _, s := range shapes {
		if best == nil || s.Area() > best.Area() {
			best = s
		}
	}
	return best
}
