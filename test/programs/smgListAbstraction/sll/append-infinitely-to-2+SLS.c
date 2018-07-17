#include <stdlib.h>
extern int __VERIFIER_nondet_int(void);
extern void __VERIFIER_assume(int);

struct SLL {
  struct SLL *next;
  int data;
};

typedef struct SLL *node;

node create_node() {
  node temp = (struct SLL *) malloc(sizeof(struct SLL));
  temp->next = NULL;
  temp->data = 0;
  return temp;
}

void free_sll(node head) {
  node p = head;
  while(p != NULL) {
    node q = p->next;
    free(p);
    p = q;
  }
}

node append_to_sll(node head, int data) {
  node new_last = create_node();
  new_last->data = data;
  if(NULL == head) {
    return new_last;
  } else {
    node last = head;
    while(NULL != last->next) {
      last = last->next;
    }
    last->next = new_last;
    return head;
  }
}

int main(void) {

  node a = create_node();
  node b = create_node();
  a->data = 5;
  b->data = 5;
  a->next = b;

  // remove external pointer
  b = NULL;

  int data = 1;
  while(__VERIFIER_nondet_int()) {
    a = append_to_sll(a, data);
  }
  
  node p = a;
  while(p != NULL) {
    __VERIFIER_assume(1 == p->data);
    p = p->next;
  }
  
  free_sll(a);
  
  return EXIT_SUCCESS;
}