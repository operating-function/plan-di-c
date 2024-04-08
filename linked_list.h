#include <stdbool.h>

typedef struct Node {
  void *ptr;
  struct Node* next;
} Node;

Node * cons(void *ptr, Node *list);

Node * reverse(Node *head);

bool null_list(Node *head);

bool member_list(void *ptr, Node *head);

void free_list(Node *head, bool free_contents);
