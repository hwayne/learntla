+++
title = "Avoiding Temporal Properties"
weight = 3
draft = true
+++

In the last section, we saw a lot of pitfalls of using temporal properties. Perhaps the biggest one is that temporal properties are much, much slower than invariants. Sometimes this is a price you have to pay. Sometimes, though, there are strategies for converting liveness properties into invariants. They aren't perfect, but if you are aware of the problems it can often be worth it.

### []

Use invariants.

### History Flags

Let's assume we want to test `<>P`. If P can only be true in a few monitorable places (for example, it only depends on one variable), we can add a `p_happened = FALSE` variable to our spec, and every time P may have switched to true, add `if P then p_happened := TRUE end if;` to that label. Then, we can express `<>P` as

```
(\A proc \in ProcSet : pc[proc] = "Done") => p_happened
```

If you are in the end state, `p_happened` must be true. That's an invariant.

A couple of caveats: This requires a check at _every_ point P can change, otherwise you can potentially have a false error. Also, this only works if you can guarantee that your algorithm terminates; if it does not, then the invariant will never be checked.

A similar technique also works for `P ~> Q`, but it's even jankier.

[note to self, does `/\ P /\ p = FALSE /\ p' = TRUE` work?]

### Termination

asdadsdsa

More stuff definitely
