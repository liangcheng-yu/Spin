## Model Checking with Spin

A mutual exclusion algorithm that works for multiple threads and offers FIFO guarantees, i.e., 
the threads get access to the critical section in the order in which they request to. 
This is in contrast to Peterson's algorithm that only works for two threads.
However, the queue lock algorithm that we will look at requires some hardware support 
in the form of an atomic `get-and-increment` action.

### Anderson’s Queue Lock Algorithm: Informal (in English) Description

Suppose that you have `NTHREADS` processes that can content for access to the critical section. 

The global state of the algorithm includes an `NTHREADS`-cell array of booleans (that we will call `queue`) 
and a global counter variable of type `byte` (that we call `cnt`).
It is important that `cnt` is of type `byte` so that the size of the state space is not too big.

Initially, `cnt` is set to `0` and `queue` is all `0`s except for the first cell which is set to `1`.

Each process first atomically gets and then increments `cnt` and stores its current value locally. 
Then it waits until the position indicated by `cnt` in the `queue` is set to true 
(since `cnt` can grow larger than the size of the array we use modulo arithmetic, i.e., `val % NTHREADS`, to get an array index). 
When its cell is set to true, it enters the critical section, sets its index in the `queue` to `false`, 
and then when it exits the critical section sets the next cell in the `queue` array to `true` (passing control to the next process).

The processes should do the above steps in an infinite loop, continuously trying to access the critical section.

### Part 1

Formally define the algorithm in Promela. This requires creating a model of the processes together with the necessary global state with which they communicate. For part one, only model two processes.

```promela
#define NTHREADS 2

bool queue[NTHREADS];
byte cnt = 0;

active [NTHREADS] proctype process()
{
    ...
}
```

Simulate your program to make sure that the model works as expected, i.e., execute a single trace, by using `spin -u100 -p -l prog.pml`, where `-u100` limits the simulation to 100 steps, and `-p` and `-l` print additional information. 

### Part 2

Augment your model with assertions and/or an LTL specifications to check the following three properties:
  - mutual exclusion in the critical section, i.e., only a single process is at the critical section at any time;
  - flag slots are used in order; and
  - starvation-freedom, i.e., a process that tries to enter the critical section will eventually enter (you might need to manually refer to all threads one by one for checking starvation freedom, meaning that your code for checking it might not be parametric with respect to `NTHREADS`).

Use `spin -run` to check that these three properties are satisfied for `NTHREADS = 2`.

Make sure to have no errors in the `spin` report.

Note: Spin might find state cycles in your program. If this error stems from unfair scheduling of processes, 
e.g., a process is never scheduled, you can safely suppress this error, by invoking `spin -run` with the `-f` flag, 
ensuring that every process will be scheduled always eventually. It might help for part 3 to think about why a cycle is found.

### Part 3

Change `NTHREADS = 3` and try to verify the properties again. Does any of them fail? Why is that?

Modify your model to suppress this error and explain why your modification 
(even though it differs from the english specification) is reasonable.

### Part 4 (Optional) 

Credits to Caleb Stanford who suggested this part.

Is it possible to have a mutual exclusion algorithm for multiple processes that does not use 
an atomic `get-and-increment` but instead only uses reads and writes.

Come up with such an algorithm and verify that it guarantees mutual exclusion.

Does your algorithm sacrifice any of the above properties?

Hint: Your might be able to use the ideas from Peterson's algorithm as a building block.

Idea: Generalize Peterson's algorithm for multiple (>=3) threads without using atomic get-and-increment, 
which is actually filter lock algorithm.

### Deliverables

Parts 1+2: Your Promela code (including assertions and ltl formulas) and the output of spin when invoked using the `-run` flag.

Part 3: Your modified Promela code (an explicit indication of the modification would be nice), 
a brief explanation of the modification and why it is necessary (could be in a Promela comment), 
and finally the output of spin when invoked with the `-run` flag.

Part 4 (Optional): Your code, spin's output, and a brief explanation of the algorithm and the sacrificed property (if any).

### Hints

If hitting the maximum default depth of spin with `error: max search depth too small`, try to increase the maximum depth using the -m flag, e.g., -m1000000, or you could try to make your state space smaller by removing unneccessary steps, unneccessary global and local variables, and by making the variable types smaller (e.g., from int to byte).
If you use the -m flag with a larger depth do mention it in the deliverable so that I know to use it to verify your code.