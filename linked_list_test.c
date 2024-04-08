#include <inttypes.h>
#include <stdio.h>
#include <stdlib.h>

#include "linked_list.h"

typedef uint64_t u64;

void print_u64_list(Node *head) {
  while (head != NULL) {
    printf("%lu\n", (u64) head->ptr);
    head = head->next;
  }
}

int main() {
  Node * test = NULL;
  printf("null_list: %s\n", null_list(test)?"true":"false");
  for (u64 i = 0; i < 10; i++) {
    test = cons((void *) i, test);
  }
  printf("null_list: %s\n", null_list(test)?"true":"false");
  printf("member_list 1:  %s\n", member_list((void *) 1,  test)?"true":"false");
  printf("member_list 11: %s\n", member_list((void *) 11, test)?"true":"false");

  printf("printing test:\n");
  print_u64_list(test);
  printf("printing rev:\n");
  Node * rev = reverse(test);
  print_u64_list(rev);

  free_list(test, false);
  free_list(rev, false);
}
