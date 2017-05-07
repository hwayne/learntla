+++
title = "Multistep Invariants"
+++

If we want to check an invariant only after a specific action, we can use `assert`. But what if we want to check an invariant only after a specific sequence of actions? For example, if we move forward and then backwards, we should be in the same position as we started. TLA+ doesn't provide a native way to test those, but we can use sequences to write our own.

Let's begin with some framework code:

```tla
variables xpos = 0, t = 0
begin
  Move:
    while t < 10 do
      either 
        xpos := xpos + 1
      or
        xpos := xpos - 1
      end either;
      t := t - 1;
    end while;
```

In order to test our invariant, we need some way of knowing the previous action, as well as how it changed the position. We can do this by adding a `history` variable, and then appending the last action and state with each step.

```tla
EXTENDS Integers, TLC, Sequences
CONSTANTS EAST, WEST, INIT

Action(action, state) == [action |-> action, state |-> state]

(*--algorithm alg
variables 
  xpos = 0, 
  t = 0,
  action = INIT
  actions = <<Action(action, xpos)>>;

begin
  Move:
    while t < 10 do
      either 
        xpos := xpos + 1
        action := EAST
      or
        xpos := xpos - 1
        action := WEST
      end either;
      actions := Append(actions, Action(acton, xpos))
      t := t - 1;
    end while;
end algorithm; *)
```

Our invariant is now definable over pairs of the most recent action.

```tla
define MoveInvariant ==
  IF Len(actions) > 2 THEN \* require two after init
  LET 
    len == Len(actions)
    recent == Subseq(actions, len-3, len)
    from == recent[1].state
    to   == recent[3].state
    a    == <<recent[2].action, 
              recent[3].action>>
  IN CASE
       a = <EAST, EAST> -> TRUE
     []a = <EAST, WEST> -> from = to
     []a = <WEST, EAST> -> from = to
     []a = <WEST, WEST> -> TRUE
```

{% notice note %}
We could have replaced two of the cases with `[] OTHERWISE -> TRUE`, but by enumerating them explicitly, any missed cases will raise an error. Pattern matching! 
{% /notice %}

### Advanced Cases

TK

## With multiple processes

TK