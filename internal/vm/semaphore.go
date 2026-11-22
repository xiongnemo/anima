package vm

import "sync"

// A semaphore counts its permits. release adds one whether or not it was
// taken here, with no most to how many there are: the count is not held to
// the permits it started with (hdl_sem_release of the native runtime).
type semaphore struct {
	mu   sync.Mutex
	free *sync.Cond
	n    int64
}

func newSemaphore(permits int64) *semaphore {
	s := &semaphore{n: permits}
	s.free = sync.NewCond(&s.mu)
	return s
}

func (s *semaphore) acquire() {
	s.mu.Lock()
	for s.n <= 0 {
		s.free.Wait()
	}
	s.n--
	s.mu.Unlock()
}

func (s *semaphore) release() {
	s.mu.Lock()
	s.n++
	s.free.Signal()
	s.mu.Unlock()
}
