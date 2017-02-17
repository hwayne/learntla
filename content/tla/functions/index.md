+++
title = "Functions"
weight = 40
+++

Beyond the basic four types in TLA+ (number, string, boolean, model value), there are two 'complex' types. The first we've already used - that's the set. The other is the function. Functions form the basis of all the 'practical' complex types, so we're going to spend some time on them. Fortunately, the theory is pretty simple.

The word 'function' can cause a lot of misunderstanding. They are not similar to functions in other languages- that's operators. Instead, functions are closer in nature to hashes or dictionaries, except that you can choose to programmatically determine the value from the key. There are two ways to define a function:

* `Function == [s \in S |-> foo]`
* `Function[s \in S] == foo`

Here, `foo` can be any equation, and can be dependent on `s`. Other than that, you have near-complete freedom. For example, you can use an infinite set:

`Doubles == [n \in Nat |-> 2 * n]`

Or multiple variables:

`Sum == [x, y \in S |-> x + y]`

You call a function with f[x], just like tuples and structs do. That's because tuples and structs _are_ functions! Specifically, tuples are just functions where the domain is 1..n. One consequence of this is that TLA+ is essentially structurally subtyped. If you write `Squares == [n \in 1..100 |-> n * n]`, then `Squares` is also by definition a tuple, and you can use sequence operators on it.

Similarly, you can write `DOMAIN F` to get the set of values F is defined on.

## Function Sets

Often we're less interested in a specific function than we are functions of a particular type. For example, we might be interested in any Caeser cipher. Since there are 26 such ciphers, it's simpler to specify the set of all corresponding functions and pull an arbitrary one from that set. The syntax for this is

`SetOfFunctions == [A -> B]`

That generates every function which maps an element of A to an element of B. A and B must be sets or expressions that evaluate to sets.

**`|->` and `->` are different.** This is going to mess you up at least once. Use `|->` when you want one function that maps the domain to a specific range. Use `->` when you want the set of functions that maps the domain to the range. 

```
S == {1, 2}
[s \in S |-> S] = [1 |-> {1, 2}, 2 |-> {1, 2}]
[S -> S] = {[1 |-> 1, 2 |-> 1], [1 |-> 1, 2 |-> 2], [1 |-> 2, 2 |-> 1], [1 |-> 2, 2 |-> 2]} 
```

Since each side is a set, you can use normal set expressions on them.

{{% q %}}
`EXTENDS Sequence` gives you the `Seq(S)` operator, which gives you the set of all sequences with a range in S. Unfortunately, you can't actually use this operator, since it will crash TLC. So let's make some better versions. First, write an operator that returns a tuple of with N copies of a set. For example `Op(S, 3) == S \X S \X S`.

{{% ans tup %}}
`Tup(S, n) == [1..n -> S]`
{{% /ans %}}

Now write an operator that returns all sequences with a range in S of length n or less.

{{% ans seq %}}
`Seq(S, n) ==  UNION {[1..m -> S] : m \in 1..n}`
{{% /ans %}}
{{%/q %}}

## Using Functions

In most cases where programmers think of using "functions", operators are actually more applicable. Operators are generally more powerful than functions. For example, you can define an operator over all subsets of the integers, but you can't do the same for functions. Additionally, you cannot use functions as invariants. In general, if you want something to take arbitrary inputs, use an operator.

What makes functions useful is that you can define them over a _finite_ domain and a finite range. In such a case it's assignable like any other variable. This, combined with set operators on the sets of functions, vastly increases the power of your specifications.

As one example, recall the code we write to simulate the three flags:

```tla
(* --algorithm flags
variables f1 \in BOOLEAN, f2 \in BOOLEAN, f3 \in BOOLEAN
begin
  with f \in {f1, f2, f3} do
      f := ~f;
  end with;
end algorithm; *)
```

This is cumbersome. What if we wanted to extend our system to have 20 flags? What if we needed another `with`? A better way is to realize that if every flag is going to be a boolean, we can then just write a function mapping flags to booleans:

```tla
(* --algorithm flags
variable flags \in [1..20 -> BOOLEAN]
begin
  with f \in DOMAIN flags do
    flags[f] := ~flags[f];
  end with;
end algorithm; *)
```

What if we wanted, as part of our initial preconditions, that no more than half of the flags were true? Since sets of functions are sets, we can use standard maps and filters on them. One way of writing this would be:

```tla
HasMoreFalseFlags(flagfunc) == 
  LET TrueFlags == { f \in DOMAIN flagfunc : flagfunc[f] }
  IN 2 * Cardinality(TrueFlags) < Cardinality(DOMAIN flagfunc)

variable flags \in { 
                     flagfunc \in [1..20 -> BOOLEAN] : 
                       HasMoreFalseFlags(flagfunc)
                   }
```

{{% q %}}
Assuming `Alphabet` is the set of all letters, and `Position[letter \in Alphabet]` is the relative position of that letter in the alphabet, find the set of all functions that are Caeser ciphers. Assume the alphabet wraps (so ROT3["z"] = "c") and a 26-letter alphabet.

(This is a good place to use sequences, but I'm trying to make things difficult.)

{{% ans cipher %}}
```tla
Range(f) == {f[x] : x \in DOMAIN f}
Ciphers == { cipher \in [1..26 -> Alphabet] :
            /\\ Range(cipher) = Alphabet \* all letters present
            /\\ \E x \in 1..26 :
                  \A l \in Alphabet:
                    cipher[((Position[l] + x) % 26) + 1] = l \* 1-indexed :(
           }
```
{{% /ans %}}
{{%/q %}}
