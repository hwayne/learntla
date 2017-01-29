+++
title = "Sequences"
weight = 2
+++

All snippets here assume you've extended `Sequences`.

### Count

Returns the number of elements of the tuple of value `value`.

```
Count(Tuple, value) == LET test(x) == x = value
                       IN Len(SelectSeq(Tuple, test))
```

### Accumulate

```
Counter(Tuple) == [val \in Range(Tuple) |-> Count(Tuple, val)]
```

Uses `Range` from function snippets. Takes advantage of the fact that tuples are also a kind of function.

### Is Sequence of Set

Determine if all elements of a sequence belong to a set.

```
sequence \in Seq(S)
```

### Tuples of length n

```
Tup(Set, n) == [1..n -> Set]
```

ie `Tup(S, 3) == S \X S \X S`.

### Sequences up to length n

We can't do `{seq \in Seq(S) : Len(seq) <= n}` because `Seq` is infinite. This is an alternative for cases where you want to work with sets of sequences and are fine capping them to a certain length.

```
SeqMaxLen(S, n) ==  UNION {[1..m -> S] : m \in 0..n}
```

ie `SeqMaxLen(S, 3) == {<<>>} \union Tup(S, 1) \union Tup(S, 2) \union Tup(S, 3)`. This can also be done with `SetReduce`:

```
SeqMaxLen(S, n) == LET _op(a, b) == Tup(S, a) \union Tup(s, b)
                   IN SetReduce(_op, 1..n, {<<>>})
```

### Map

```
SeqMap(Op(_), seq) == [x \in DOMAIN seq |-> Op(seq[x])]
```
