+++
title = "Processes"
weight = 1
+++

### Delayed Processes
#### Problem
You want process A to only start after a certain thing is true.
#### Solution
```
process A ...
begin
  Wait:
    await \* expression
    \* finish
```

### Sequential Processes
#### Problem
You want to make sure that process B runs after process A finishes.
#### Solution
```
process B ...
begin
  Wait:
    await pc["A"] = "Done"; \* or other label string
    \* finish
```

### Multiple processes on the same model value

#### Problem 

You have a system where for every user U, actions A and B both occur, but in an arbitrary order. If you model this with processes, TLC will lump them both in a case statement and cause a silent error.

#### Solution

Create an operator to generate unique structures for each case.
```
CONSTANT Users

define
  UserProc(proc) == [ u : Users, p : {proc} ]
end define;

process A \in UserProc("A")
process B \in UserProc("B")
```

Note that if Users is itself a struct, then you have to call a user with `Users[self.u]`.
