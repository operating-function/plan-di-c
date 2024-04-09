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

plan: linked_list.o plan.c
	gcc $^ -o $@

plan_with_tracing: plan_with_tracing.c
	gcc $^ -o $@

plan_debug: linked_list.o plan.c
	gcc -g -O0 $^ -o $@
