#define N 5
byte counter 

active [N] proctype Proc() {
    do
    :: (counter % N == _pid) -> counter++
    od
}

// Spin data type overflows.
ltl invariant { [] (counter <= 255)}