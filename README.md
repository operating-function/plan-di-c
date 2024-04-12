# Simple PLAN Implementation in C

This is a simple, naive implementation of PLAN in C.  This is basically
a port of `PLAN_SPEC.txt`.

## make bsdnt/

```
cd bsdnt/
./configure
make        # to just build
make check  # to run tests
```

## building

```
make plan
```

## testing

```
make test
```

## debugging

```
make plan_debug
gdb ./plan_debug
<...>
(gdb) run < <(echo "(0 5 (#2 4))")
<...>
```
