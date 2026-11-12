package flow

import "fmt"

type Weekday int

const (
	Sunday Weekday = iota
	Monday
	Tuesday
)

func (d Weekday) String() string {
	return [...]string{"Sun", "Mon", "Tue"}[d]
}

func collatz(n int) (steps int) {
	for n != 1 {
		if n%2 == 0 {
			n /= 2
		} else {
			n = 3*n + 1
		}
		steps++
	}
	return
}

func search(grid [][]int, target int) (int, int, bool) {
outer:
	for i, row := range grid {
		for j, v := range row {
			switch {
			case v == target:
				return i, j, true
			case v > target:
				continue outer
			}
		}
	}
	return -1, -1, false
}

func main() {
	for i := range 3 {
		fmt.Println(Weekday(i), collatz(i+6))
	}
	if i, j, ok := search([][]int{{1, 2}, {3, 4}}, 3); ok {
		fmt.Println(i, j)
	}
}
