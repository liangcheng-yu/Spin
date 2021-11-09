int counter 

active [5] proctype Proc() {
    (counter == _pid) -> counter++
    if
    :: (_pid == 3) -> assert(counter == 4)
    :: else -> skip
    fi
}