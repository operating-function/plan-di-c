#include <stdlib.h>
#include <stdbool.h>

#include "linked_list.h"

Node * cons(void *ptr, Node *list) {
  struct Node* node = (struct Node*)malloc(sizeof(struct Node));
  node->ptr = ptr;
  node->next = list;
  return node;
}

Node * reverse(Node *head) {
  Node *ret = NULL;
  while (head != NULL) {
    ret = cons(head->ptr, ret);
    head = head->next;
  }
  return ret;
}

void free_list(Node *head, bool free_contents) {
  Node *tmp;

  while (head != NULL) {
    tmp = head;
    head = head->next;
    if (free_contents) free(tmp->ptr);
    free(tmp);
  }
}
