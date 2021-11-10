#define NTHREADS 2

bool queue[NTHREADS] = {true, false};
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
    }

    // Block until true to enter critical session
    (queue[cnt_local%NTHREADS] == true);

    assert(cnt_local%NTHREADS == expected_next_slot % NTHREADS)
    expected_next_slot++

    in_crit++
crit: assert(in_crit == 1)
    queue[cnt_local%NTHREADS]=false
    in_crit--

    queue[(cnt_local+1)%NTHREADS]=true
    goto again
}

ltl invariant { [] !(process[0]@crit && process[1]@crit) && [] (<> process[0]@crit) && [] (<> process[1]@crit)}
