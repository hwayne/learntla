+++
title = "Procedures and Macros"
weight = 3
+++

If you have multiple processes, you might eventually want to share code between them. Since we’re engineers we want to keep things DRY, and the simplest way to do that is with macros and procedures.

### Macros

Macros are the general catch-all code inliner. You define them with

```
macro Name(var1, ...)
begin
 \* stuff
end macro;
```

And call them with `Name(value1, ...)`. Simple. There's just a few caveats you have to keep in mind:

1. A macro is shorthand code, not its own process. So they can't have labels, `with` statements, while loops, etc. 
1. This happens inline. [[ TODO example. ]]

Macros must be defined after any `define` block and before any processes.

### Procedures

Procedures are a little more difficult to both write and use. In return, though, you get two benefits. One, a procedure can have internal variables. Two, you can have labels in them.

```
procedure Name(arg1, ...)
variables var1 = ... \* This cannot be \in, only =
begin
  Label:
  \* stuff
  return;
end procedure;
```

The return just ends the procedure. If your procedure never reaches it, then it's an error. It won't return any value (really, nothing does).

In order to call a procedure, you have to explicitly use `call Name(val1, ...);`, and the following line must be a label or a `return` (if you called it from another procedure).

{{% notice warning %}}
 If you want to use procedures you _must_ `EXTEND Sequences`.
{{% /notice %}}

Procedures must be defined after any macros and before any processes.

### Order of operations

PlusCal enforces a strict ordering of its blocks. The `define` block hass to come before any macros, which has to come before any procedures, which has to come before any processes.

### Macros vs Procedures

So when should you use which? Macros are faster and less complicated. If you can use them, use them. Use procedures when you have multiple separate processes that can do the same actions.

EXAMPLE
