package worker

import (
	"context"
	"sync"
	"time"
)

type Job struct {
	ID   int
	Data []byte
}

type Result struct {
	Job   Job
	Size  int
	Error error
}

// Pool runs n workers over the jobs until the context is done.
func Pool(ctx context.Context, n int, jobs <-chan Job) <-chan Result {
	results := make(chan Result)
	var wg sync.WaitGroup
	for i := 0; i < n; i++ {
		wg.Add(1)
		go func(id int) {
			defer wg.Done()
			for {
				select {
				case <-ctx.Done():
					return
				case j, ok := <-jobs:
					if !ok {
						return
					}
					results <- Result{Job: j, Size: len(j.Data)}
				case <-time.After(time.Second):
					continue
				}
			}
		}(i)
	}
	go func() {
		wg.Wait()
		close(results)
	}()
	return results
}

var counter = struct {
	sync.Mutex
	n map[string]int
}{n: map[string]int{}}

func Count(key string) int {
	counter.Lock()
	defer counter.Unlock()
	counter.n[key]++
	return counter.n[key]
}
