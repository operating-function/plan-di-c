This is a simple PLAN interpreter that is capable of compiling the
sire compiler.

In order to run the test, run:

    $ bash repl.sh

In order to get (slowly) a sire repl, run:

    $ gcc -O3 plan.c
    $ cat sire.sire /dev/stdin | ./a.out
