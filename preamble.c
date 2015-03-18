#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>

typedef void * (*raw_fun)(void **);

typedef struct {
  raw_fun fun;
  int numArgs;
  void **args;
} clos;

void *apply(void *fun, void *arg){
  clos *c = (clos *) fun;
  c->args[c->numArgs - 1] = arg;
  return c->fun(c->args);
}

void *mkZero(){
  int *ptr = malloc(sizeof(int));
  *ptr = 0;
  return (void *) ptr;
}

void *inc(void *i){
  int *ptr = malloc(sizeof(int));
  *ptr = *((int *) i) + 1;
  return (void *) ptr;
}

void *dec(void *i){
  int *ptr = malloc(sizeof(int));
  *ptr = *((int *) i) - 1;
  return (void *) ptr;
}

int isZero(void *i){
  return *((* int) i) == 0
}

void *mkClos(raw_fun f, int numArgs, ...){
  clos *c = malloc(sizeof(raw_fun));
  c->fun = f;
  c->numArgs = numArgs + 1;
  c->args = malloc(sizeof(void*) * (numArgs + 1));
  va_list l;
  va_start(l, numArgs);
  for(int i = 0; i < numArgs; ++i)
    c->args[i] = va_arg(l, void *);
  return (void *) c;
}

void call(raw_fun f){
  int *i = (int *) f(NULL);
  printf("%d\n", *i);
}
