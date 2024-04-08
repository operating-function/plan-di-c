all: plan plan_with_tracing

.PHONY: test
test: plan
	bash ./test.sh

linked_list.o: linked_list.h linked_list.c
	gcc -g -c $^

plan: linked_list.o plan.c
	gcc $^ -o $@

plan_with_tracing: plan_with_tracing.c
	gcc $^ -o $@

plan_debug: linked_list.o plan.c
	gcc -g -O0 $^ -o $@
