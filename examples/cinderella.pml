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
#define n 6
#define k 10
#define b 29
#define c 1


free env int(0, k) more[n];
sys int(0, b) bucket[n];
/* index of first bucket out of c to empty */
sys int(0, n) start;

/* the stepmother pours k more liters in every turn */
assume ltl { [](
	more[0] + more[1] + more[2] + more[3] + more[4] + more[5] <= k
) }


assert sys proctype cinderella(){
	int(0, n) i;
	do
	:: atomic{
		/* each turn, she empties c adjacent buckets */
		((X start) < n);
		i = 0;
		do
		:: (i < c);
			if
			:: (start + i < n);
				bucket[start + i] = 0
			:: else;
				bucket[start + i - n] = 0
			fi;
			i = i + 1
		:: else; break
		od;
		/* adds incoming water */
		i = 0;
		do
		:: (i < n);
			bucket[i] = bucket[i] + more[i];
			i = i + 1;
		:: else; break
		od;
		}
	od
}
