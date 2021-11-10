// Observation:
//   When NTHREADS=3, the properties of slots are used in order and mutual exclusion fail.
// 
// Why: 
// Note that Spin will overflow for cnt variable, and this results in unexpected behavior
//   when combined with modulo arithmetic.
// When NTHREADS=2, it works because 254%2==0, 255%2==1, 266(0)%2==0 where 266 overflows to 0,
//   that is, ...->0->1->0->... therefore the slots are used in order and mutual exclusion is preserved.
// When NTHREADS=3, however, 253%3==1, 254%3==2, 255%3==0, 266(0)%3==0, that is, ...->1->2->0->0->...
//   here the slots are NOT used in order upon byte overflow, and breaks mutual exclusion.
// 
// Solution:
//   We could wrap the cnt so that the overflow period is a multiple of NTHREADS.
//   This patch doesn't change any semantics of the locking algorithm and resolves the issue of overflow mismatch with modulo.

#define NTHREADS 3

bool queue[NTHREADS] = {true, false, false};
byte cnt = 0;
byte in_crit;
// Auxilliary variable to assert that flag slots are used in order
byte expected_next_slot = 0;

active [NTHREADS] proctype process()
{
    byte cnt_local

again:
    // Note: get-and-increment rather than increment-and-get :)
    atomic{
        cnt_local = cnt
        cnt++
        // Patch: wrap cnt with cycle period NTHREADS (or its multiples)
		if
		:: (cnt == NTHREADS) -> cnt = 0
		:: else -> skip
		fi
    }

    // Block until true to enter critical session
    (queue[cnt_local%NTHREADS] == true);

    assert(cnt_local % NTHREADS == expected_next_slot % NTHREADS)
    expected_next_slot++
    // Consistent with cnt
	if
	:: (expected_next_slot == NTHREADS) -> expected_next_slot=0
	:: else -> skip
	fi

    in_crit++
crit: assert(in_crit == 1)
    queue[cnt_local%NTHREADS]=false
    in_crit--

    queue[(cnt_local+1)%NTHREADS]=true
    goto again
}

ltl invariant { [] !(process[0]@crit && process[1]@crit) && 
                [] (<> process[0]@crit) && [] (<> process[1]@crit) && [] (<> process[2]@crit)}

