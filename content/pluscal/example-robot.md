+++
title = "[Example: Direction Robot]"
weight = 6
+++

We now have all of the pieces we need, so let's put it all into practice.

## The Problem

There are 10 spaces on a board, labeled 0-9. Your robot starts at space 0 and there is a flag on some random space. Each move, you can do one of 

- Change position by one
- Determine whether the flag greater, less than, or equal to your current position
- Pick up the flag (if you're on the square).

Write an algorithm that guarantees you always pick up the flag.

### First Steps

Man, this would have been a lot easier if I had introduced sequences already. Then again, we don't exactly _need_ sequences for this, so w/e. Here's a first draft:

```
EXTENDS Integers
(* --algorithm flag

variables board = 0..9, pos = 0, flag \in board, has_flag = FALSE;
begin
  while ~has_flag do
if pos = flag then has_flag := TRUE; else pos := pos + 1; end if
  end while;
end algorithm; *)
```

As a simple invariant for this model, let's ensure we never leave the board: `pos \in board`. If we run the model, we see this works out.

Now to add the first twist: _The robot starts at a random space on the board._ Changing our algorithm to match this is pretty simple. All we have to do is replace `post = 0` with `pos \in board`. As soon as we do this, though, we get an error:

[]

TLC found a counterexample: if the robot starts at a higher number than the flag, it will never reach the flag. Instead, we have to determine the direction of the flag and then start moving in that direction:

```
EXTENDS Integers
(* --algorithm flag

variables board = 0..9, pos \in board, flag \in board, has_flag = FALSE;
begin
  while ~has_flag do
  if pos = flag then has_flag := TRUE; 
  else 
    Ping:
      if pos < flag 
      then pos := pos + 1; 
      else pos := pos - 1;
      end if;
  end if;
  end while;
end algorithm; *)
```

### Making things way more complicated

_For every space the robot moves, the flag can choose to move one space._

```
either
  with i \in {1, -1} do
    flag := flag + i;
  end with
or
  skip;
end either
```

IF we run this, we immediately get an error: the flag can move to `-1` and then the robot will break an invariant trying to reach it.
```
if flag + i \in board then flag := flag + i
```

Second
