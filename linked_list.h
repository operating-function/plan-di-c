#include <stdbool.h>

typedef struct Node {
  void *ptr;
  struct Node* next;
} Node;

Node * cons(void *ptr, Node *list);

Node * reverse(Node *head);

void free_list(Node *head, bool free_contents);
