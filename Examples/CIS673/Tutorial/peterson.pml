// Algorithm: https://en.wikipedia.org/wiki/Peterson%27s_algorithm
bool flags[2];  // Process n interested in entering the critical section
int in_crit;
bool turn;  // The field indicating the victim upon contention


active [2] proctype proc(){
    bool temp
again:
    flags[_pid] = 1;  // I am interested
test:    turn = _pid;  // Key: when contending, the process setting turn late should be polite ("but you go first")
    (flags[(1 - _pid)] == 0 || turn == (1 - _pid));  // Key idea of Peterson is this OR condition, if only first conditon, we could have a deadlock where both mark interests before checking the guard
    
    temp = turn;

    // Critical section
    in_crit++
// Two ways to verify the critical session
// 1. Use label and specify the invariant
// 2. Use aux global var in_crit
crit: assert(in_crit == 1)
    in_crit--
    
    flags[_pid] = 0;
    goto again
}

// Must verify with `spin -run -f` which queries Spin for fair scheduling (by default, Spin doesn't schedule fairly, and will stick on one process repeatedly in this scenario), otherwise, fails
// ltl invariant { [] !(proc[0]@crit && proc[1]@crit) && [] (<> proc[0]@crit) && [] (<> proc[1]@crit)}
// Fails
// ltl invariant { [] !(proc[0]@crit && proc[1]@crit) && [] (<> proc[0]@crit) && [] (<> proc[1]@crit) && [] (proc[0]@test -> (! proc[1]@crit U proc[0]@crit))}