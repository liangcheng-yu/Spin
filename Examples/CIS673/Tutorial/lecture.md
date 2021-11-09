# Lecture on Spin and Promela

*Concise fill-in of the exercises of the nice CIS 673 tutorial (https://github.com/angelhof/penn-cis673-hw-spin) by Konstantinos Kallas.*

The lecture combines material from the following resources:
- Ulrik Nyman's slides that give a quick reference on most syntactic constructs http://people.cs.aau.dk/~ulrik/teaching/E10/ModelChecking/spin.pdf
- Theo Ruys' slides on a Spin and Promela tutorial https://spinroot.com/spin/Doc/SpinTutorial.pdf
- Spin Verification Examples and Exercises http://web.mit.edu/spin_v6.4.7/Doc/1_Exercises.html


## Installation

Make from source [official Github repo](https://github.com/nimble-code/Spin):
```
make; sudo cp Src/spin /usr/local/bin
spin -V
```
Alternatively: https://spinroot.com/spin/Man/README.html (which has more user-friendly GUI for step-by-step debugging)


## Basic Promela Language Syntax and Program Structure

A lot of the constructs are redundant (you can do things in many ways) 
  but I want to give you a whirlwind tour first so that 
  you are able to understand examples and documentation that you find online.

Promela's syntax borrows from C but it is significantly different.



### Processes

The fundamental building blocks in Promela programs are processes.

A process looks like this:

```promela
proctype ExampleProcess(int input) {
    int out;
    byte out2;
    // Process body
    ...
}
```

The keyword that we use to define processes is `proctype` together with a name and arguments.
Note that this is a process type, because we can then start many instances (processes) of that type.

Processes look similar to functions but they are not.
A process can be started, and then it runs concurrently with other processes in the system.
This is in contrast to functions, which when called, 
  we simply pass control to them until they finish execution
  and then they pass execution back.

Processes have local variables and arguments, that are defined similarly to C using their type and name.
Here `int` is the classic 32 bit integer and `bit` is a type with only two values, 0 and 1.


We can then start a process of type `ExampleProcess` using the `init` function that exists in Promela programs.

```promela
init {
    run ExampleProcess(2);
    run ExampleProcess(3);
}
```


We can also run processes without explicitly starting them (`run`ning them in the `init`)
  by adding the `active` keyword with a number in their definition.

```promela
active [3] proctype ExampleProcess(int input) {
    // body
}
```

This `run`s 3 processes of type `ExampleProcess` and initializes their parameters to 0.




### Promela Basic Constructs

Processes do not have return values, and so processes communicate with each other using global variables.

Global variables are declared the same way as local variables in the global scope. 

```promela
int counter

active [5] proctype Proc() {
    //
}
```


Let's now look at a program where 5 processes increment a counter, one by one. 

```promela
int counter 

active [5] proctype Proc() {
    (counter == _pid) -> counter++
}
```

The variable `_pid` is a special variable that each process can use internally. 
Pids start from `0` and so here our processes will have the pids 0, 1, 2, 3, 4 respectively.

The test `(counter == _pid)` is a check that will block until it is satisfied. It behaves almost like a busy loop that waits until that is true.

Then the final construct is the arrow `->` which is often used in promela after tests
  but it actually behaves the the same as a sequencing operator.

In fact, we could even write the body of the above process type as:
```
    (counter == _pid);
    counter++
```




So in the above program, each process blocks until its turn is reached 
  (the counter becomes equal to its pid) 
  and then simply increments the counter, passing control to the next process.

In the end, we would expect the counter to be equal to 5 right?
We can make an assertion to check that.



```promela
int counter 

active [5] proctype Proc() {
    (counter == _pid) -> counter++
    if
    :: (_pid == 4) -> assert(counter == 5)
    :: else -> skip
    fi
}
```

Here we have some more new constructs.

First, we have an `if` statement. In promela, `if` statements contain cases that are indicated by `::` and followed by a test.

Note that the tests do not need to be mutually exclusive, and if more than one holds, then any one can execute nondeterministically.

The keyword `else` simply matches if no other guard matches. 
Note that it is different from not having a guard at all (or having a guard that always matches).

Finally, we have the `assert` statement that checks whether its condition holds.
Asserts are used to specify properties that need to hold in the code.





So the above program does the counter increments as before, and then the last process (`pid == 4`)
  checks whether the counter is indeed 5. 
  
Let's do a small divergence and run it with `spin` to see if that works.

We can do that simply by invoking `spin` with the flag `-run` and the name of our file `counter_ex.pml`:

```sh
spin -run counter_ex.pml
```

You can use the `-bfs` flag with `spin -run` when debugging so that spin uses BFS to find the shortest counterexample trace.

When invoking `spin` with `-run`, it verifies that there is no error (for example assertion violation).
To be more precise, it generates a verifier C file, that it then compiles and runs.

By inspecting the output, we see that there is no assertion violation so we are good!
  A summary of the output report can be found in slide 36 in Ruy's slides (https://spinroot.com/spin/Doc/SpinTutorial.pdf).

Q: What would happen if we change the guard and assertion to `(_pid == 3) -> assert(counter == 4)`? Would that be correct too?



Before running `spin` let's try to figure out ourselves.



Well it fails! What a surprise!
This is because in promela, processes steps can interleave, 
  and therefore in between the guard and the actual `assert`, the next process might have executed its increment.

Let's now do another small divergence and try to figure out why it failed (and if our initial explanation was correct).

If we look at the directory where the first `spin` verification failed,
  we see that there is a file with the same name and a `.trail` suffix.

This file contains a counterexample trail that `spin` can read and explain what failed.

We can do that as follows:

```sh
spin -t -p counter_ex.pml
# or
spin -t -p -l counter_ex.pml
```

The flag `-t` follows a `.trail` file with the name of the original file, and `-p` prints every step in this trail file.

We can now follow through the steps of the counterexample trail and understand what the issue is.

But how can we fix the failing assert above?
We can use `atomic` blocks to batch together statements. They ensure that a process cannot be scheduled out while being in the `atomic` block.

```promela
int counter 

active [5] proctype Proc() {
    atomic{
        (counter == _pid) -> counter++
        if
        :: (_pid == 3) -> assert(counter == 4)
        :: else -> skip
        fi
    }
}
```

By running `spin -run counter_ex.pml` we see that it now holds and we are good to go.

In practice, don't abuse the usage of atomic to make sure that the modeling in SPIN mirrors the real-world environment.


### Loops

```promela
do
:: guard -> ...
:: guard -> ...
:: guard -> ...
od
```

The same rules that apply to `if`s apply to them too (nondeterminism, `else`, etc).
That is, the loop execution is non-deterministically among holding guards.

```promela
do
:: (1) -> ...
:: (1) -> ...
od
```

Finally, we can have `break` statements (that exit a loop), 
  and also we can have `goto` statements and labels that change execution flow.

Example:

```promela
    x = 0
S2: x++;
    y = y + x;
    goto S2;
```

Labels can sometimes be useful, e.g., when defining process state machines. 

We will see some examples of labels and loops usage below.





## LTL Specifications

We now shift our focus to LTL specifications. 
You have already seen LTL specs in the course, so now we simply show how to write them in Promela.

First, the standard LTL operators can be written in Promela straightforwardly as so:
- Always can be written like this `[]`, e.g., `[] (x == y)`
- Eventually can be written like this `<>`, e.g., `<> (x == 2)`
- Until can be written like this `U`, e.g., `x = y U found = true`

The way to add an LTL specification in a Promela program is simply by adding an `LTL invariant`.


Let's get back to the counter example and try to replace the `assert` with an LTL invariant.

```promela
int counter 

active [5] proctype Proc() {
    (counter == _pid) -> counter++
}

LTL invariant { Your invariant here :) }
```

Q: What is an invariant that describes the property that we tried to check with out assert? 
   Namely, that the in the end, the counter is 5?

`ltl invariant {<> (counter==5)}`



Q: Can we extend the invariant with a property about what values counter cannot reach?

`ltl invariant { <> (counter==5) && [] (counter <= 5) }`


Now let's extend the processes to loop as follows:

```promela
#define N 5
int counter 

active [N] proctype Proc() {
    do
    :: (counter % N == _pid) -> counter++
    od
}
```

Spin uses C preprocessor under the hood, hence it allows `define` macros similarly to C.

Q: What values can counter reach? What is an invariant that holds here?



## Example: Peterson's mutual exclusion algorithm implementation

