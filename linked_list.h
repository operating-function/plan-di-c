#include <stdbool.h>
#include <inttypes.h>

typedef uint64_t u64;

typedef struct Node {
  void *ptr;
  struct Node* next;
} Node;

Node * cons(void *ptr, Node *list);

Node * reverse(Node *head);

bool null_list(Node *head);

bool member_list(void *ptr, Node *head);

u64 length_list(Node *head);

void free_list(Node *head, bool free_contents);
