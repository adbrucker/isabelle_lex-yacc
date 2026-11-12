// Package main is the traditional first program.
package main

import (
	"fmt"
	"os"
)

const greeting = "Hello, "

var names = []string{"Go", "Isabelle"}

func main() {
	for i, name := range names {
		fmt.Println(i, greeting+name)
	}
	if len(os.Args) > 1 {
		fmt.Fprintln(os.Stderr, "unexpected arguments:", os.Args[1:])
		os.Exit(2)
	}
}
