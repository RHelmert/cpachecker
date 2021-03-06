#include <stdlib.h>

typedef struct node {
  struct node* next;
  int data;
} *SLL;

SLL node_create(int data) {
  SLL temp = (node *) malloc(sizeof(struct node));
  temp->next = NULL;
  temp->data = data;
  return temp;
}

void sll_destroy(SLL head) {
  while(head) {
    SLL temp = head->next;
    free(head);
    head = temp;
  }
}

void _assert(int x) {
  if(!x) {
    node_create(-1);
  }
}

int main(void) {

  const int data_1 = 5;
  const int data_2 = 7;

  SLL a = node_create(data_1);
  SLL b = node_create(data_2);
  a->next = b;

  b = NULL;
  _assert(data_1 == a->data);
  
  b = a->next;
  _assert(data_2 == b->data);

  b = NULL;
  sll_destroy(a);
    
  return 0;
}
