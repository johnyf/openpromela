/*
 * ARM AMBA AHB case study.
 *
 * Adapted from [2] as described in [1].
 *
 *
 * References
 * ==========
 *
 * [1] Ioannis Filippidis and Richard M. Murray
 *     "Revisiting the AMBA AHB bus case study"
 *     California Institute of Technology, 2015
 *     http://resolver.caltech.edu/CaltechCDSTR:2015.004
 *
 * [2] Roderick Bloem, Barbara Jobstmann, Nir Piterman,
 *     Amir Pnueli, Yaniv Sa'ar
 *     "Synthesis of reactive(1) designs"
 *     Journal of computer and system sciences
 *     Vol.78, No.3, pp.911--938, 2012
 */

#define N 2  /* N + 1 masters */
#define SINGLE 0
#define BURST4 1
#define INCR 2


/* variables of masters and slaves */
/* A4: initial condition */
free env bool ready = false;
free env int(0, 2) burst;
free env bool request[N + 1] = false;
free env bool grantee_lockreq = false;
free env bool master_lockreq = false;

/* arbiter variables */
/* G11: sys initial condition */
free bool start = true;
free bool decide = true;
free bool lock = false;
free bool lockmemo;
free int(0, N) master = 0;
free int(0, N) grant;

/* A2: slaves must progress with receiving data */
assume ltl { []<> ready }

/* A3: dropped, weakening the assumptions */

/* A1: if current master is granted locked access,
 * then it must progress by withdrawing the lock request.
 */
assume env proctype withdraw_lock(){
	progress:
	do
	:: lock;
		do
		:: ! master_lockreq'; break
		:: true /* wait */
		od
	:: else
	od
}


assert ltl {
	[](
		/* G1: new access starts only when slave is ready */
		(start' -> ready)
		/* G4,5: current master and lock updated
		 * only when communicating slave signals
		 * that it completed receiving data.
		 */
		&& (ready -> ((master' == grant) && (lock' <-> lockmemo')))
		/* G6: current master and locking may change only
		 * when an access starts, and remain invariant otherwise
		 */
		&& (! start' -> (
			(master' == master) &&
			(lock' <-> lock)))
		/* G7: when deciding, remember if the requestor
		 * requested also locking.
		 * when implementing the circuit, store
		 * previous lock requests:
		 * grantee_lockreq' = (--X lockreq)[grant]
		 */
		&& ((--X decide) -> (lockmemo' <-> grantee_lockreq'))
		/* G8: current grantee and locking memo
		 * remain invariant while not deciding.
		 */
		&& ( (! decide) -> (grant' == grant) )
		&& ( (! --X decide) -> (lockmemo' <-> lockmemo) )
		/* G10: only a requestor can become grantee */
		&& ((grant' == grant) || (grant' == 0) || request[grant'])
	)
}

/* all properties must hold synchronously */
sync{

/* G9: weak fairness */
assert sys proctype fairness(){
	int(0, N) count;
	do
	:: (! request[count] || (master == count));
		if
		:: (count < N) && (count' == count + 1)
		:: (count == N) && (count' == 0);
			progress: skip
		fi
	:: else
	od
}

/* G2: if locked access of unspecified length starts,
 * then locking shall be withdrawn before starting
 * another access.
 */
assert sys proctype maintain_lock(){
	do
	:: (lock && start && (burst == INCR));
		do
		:: (! start && ! master_lockreq'); break
		:: ! start
		od
	:: else
	od
}

/* G3: for a BURST4 access,
 * count the "ready" time steps.
 */
assert sys proctype count_burst(){
	int(0, 3) count;
	do
	:: (start && lock &&
		(burst == BURST4) &&
		(!ready || (count' == 1)) &&
		(ready || (count' == 0)) );
		do
		:: (! start && ! ready)
		:: (! start && ready && (count < 3) &&
			(count' == count + 1))
		:: (! start && ready && (count >= 3)); break
		od
	:: else
	od
}

}
