all: plan plan_with_tracing

.PHONY: test
test: plan
	bash ./test.sh

plan: plan.c
	gcc $^ -o $@

plan_with_tracing: plan_with_tracing.c
	gcc $^ -o $@

plan_debug: plan.c
	gcc -g $^ -o $@
