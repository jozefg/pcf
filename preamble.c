#include <stdlib.h>
#include <stdio.h>

typedef void * (*raw_fun)(void **);

typedef struct {
  raw_fun fun;
  int numArgs;
  void **args;
} clos;

void *apply(void *fun, void *arg){
  clos *c = (clos *) fun;
  c->args[c->numArgs] = arg;
  return c->fun(c->args);
}

void *mkZero(){
  int *ptr = malloc(sizeof(int));
  *ptr = 0;
  return (void *) ptr;
}

void *dec(void *i){
  int *ptr = malloc(sizeof(int));
  *ptr = *((int *) i) + 1;
  return (void *) ptr;
}

void *inc(void *i){
  int *ptr = malloc(sizeof(int));
  *ptr = *((int *) i) - 1;
  return (void *) ptr;
}
