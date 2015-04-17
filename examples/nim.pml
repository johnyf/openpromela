#define N_HEAPS 10
#define HEAP_SIZE 10

free env int(0, N_HEAPS) Alice_heap;
free env int(1, HEAP_SIZE) Alice_removes;

free sys int(0, N_HEAPS) Bob_heap;
free sys int(1, HEAP_SIZE) Bob_removes;
sys bit turn = 0; /* 0 = env, 1 = sys */

assert sys proctype board(){
	int(0, HEAP_SIZE) heap[N_HEAPS + 1] = HEAP_SIZE;
	int(0, N_HEAPS) j;
	int(0, HEAP_SIZE) k;
	do
	::
		if
		:: turn == 0;
			j = Alice_heap;
			k = Alice_removes
		:: turn == 1;
			j = Bob_heap;
			k = Bob_removes
		fi;
		if
		:: (0 < k) && (k <= heap[j]);
			heap[j] = heap[j] - k;
			turn = 1 - turn;
		:: else
		fi;
	od
}

assert ltl { []<>(turn == 1) }
