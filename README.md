# Simple PLAN Implementation in C

This is a simple, naive implementation of PLAN in C.  This is basically
a port of `PLAN_SPEC.txt`.

## debugging

```
make plan_debug
gdb ./plan_debug
<...>
(gdb) run < <(echo "(0 5 (#2 4))")
<...>
```
