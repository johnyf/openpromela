/*
 * Cinderella-stepmother game
 * proposed by Rajeev Alur.
 *
 * The stepmother distributes
 * k liters, and each bucket overflows
 * at b liters.
 *
 * Note that b here is k * b in
 * the original formulation.
 * This is done to avoid fractions.
 * The result is equivalent.
 */
#define n 5
#define k 4
#define b 7
#define c 2


free env int(0, k) more[n];
sys int(0, b) bucket[n];
/* index of first bucket out of c to empty */
sys int(0, n) start;

/* the stepmother pours k more liters in every turn */
assume ltl { [](
	more[0] + more[1] + more[2] + more[3] + more[4] <= k
) }


assert sys proctype cinderella(){
	int(0, n) i;
	do
	:: atomic{
		/* each turn, she empties c adjacent buckets */
		(X start < n) && (X i == 0);
		do
		:: (i < c);
			if
			:: (start + i < n) &&
				(X bucket[start + i]) == more[start + i]
			:: (start + i >= n) &&
				(X bucket[start + i - n]) == more[start + i - n]
			fi;
			i = i + 1
		:: (c <= i) && (i < n);
			if
			:: (start + i < n) &&
				(X bucket[start + i]) == bucket[start + i] + more[start + i]
			:: (start + i >= n) &&
				(X bucket[start + i - n]) == bucket[start + i - n] + more[start + i - n]
			fi;
			i = i + 1
		:: else; break
		od;
		}
	od
}
