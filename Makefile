CFLAGS = -O3 -Wall -Werror -fdiagnostics-color=always

all: plan plan_debug

.PHONY: clean
clean:
	rm *.o

.PHONY: quick_test
quick_test: plan
	perf stat ./plan foo.in

.PHONY: quine
quine: plan
	perf stat ./plan < sire-in-sire.sire

.PHONY: test
test: plan
	perf stat ./plan test.sexp

linked_list.o: linked_list.h linked_list.c
	gcc $(CFLAGS) -c $^

linked_list_test: linked_list.o linked_list_test.c
	gcc $(CFLAGS) $^ -o $@

plan: bsdnt/build/nn.o bsdnt/build/zz0.o bsdnt/build/nn_linear.o bsdnt/build/nn_quadratic.o bsdnt/build/nn_subquadratic.o bsdnt/build/helper.o linked_list.o plan.c
	gcc $(CFLAGS) $^ -o $@ -lm

plan_debug: bsdnt/build/nn.o bsdnt/build/zz0.o bsdnt/build/nn_linear.o bsdnt/build/nn_quadratic.o bsdnt/build/nn_subquadratic.o bsdnt/build/helper.o linked_list.o plan.c
	gcc -pg -g -O0 $^ -o $@ -lm
