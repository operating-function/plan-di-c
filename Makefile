all: plan plan_with_tracing

.PHONY: clean
clean:
	rm *.o

.PHONY: test
test: plan
	bash ./test.sh

linked_list.o: linked_list.h linked_list.c
	gcc -g -c $^

linked_list_test: linked_list.o linked_list_test.c
	gcc -g $^ -o $@

plan: bsdnt/build/nn.o bsdnt/build/zz0.o bsdnt/build/nn_linear.o bsdnt/build/nn_quadratic.o bsdnt/build/nn_subquadratic.o bsdnt/build/helper.o linked_list.o plan.c
	gcc $^ -o $@ -lm

plan_with_tracing: plan_with_tracing.c
	gcc $^ -o $@

plan_debug: bsdnt/build/nn.o bsdnt/build/zz0.o bsdnt/build/nn_linear.o bsdnt/build/nn_quadratic.o bsdnt/build/nn_subquadratic.o bsdnt/build/helper.o linked_list.o plan.c
	gcc -g -O0 $^ -o $@ -lm
