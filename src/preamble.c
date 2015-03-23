#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#define EMPTY {.size = NULL, .blackhole = NULL, .ptr = NULL}
#define INT_SIZE sizeof(int)
#define CLOS_SIZE sizeof(clos)

typedef struct {
  void *ptr;
  int *blackhole;
} sized_ptr;

typedef sized_ptr (*raw_fun)(sized_ptr *);

typedef struct {
  raw_fun fun;
  int numArgs;
  sized_ptr *args;
} clos;

sized_ptr apply(sized_ptr fun, sized_ptr arg){
  if(*fun.blackhole || *arg.blackhole) exit(1);

  clos *c = (clos *) fun.ptr;
  c->args[c->numArgs - 1] = arg;
  return c->fun(c->args);
}

sized_ptr mkZero(){
  int *ptr = malloc(sizeof(int));
  int *hole = malloc(sizeof(int));

    *ptr = 0;
  *hole = 0;

  sized_ptr new_ptr = {.ptr = (void *) ptr, .blackhole = hole};
  return new_ptr;
}

sized_ptr inc(sized_ptr i){
  int *ptr = malloc(sizeof(int));
  int *hole = malloc(sizeof(int));

  if(*i.blackhole) exit(1);

  *ptr = *((int *) i.ptr) + 1;
  *hole = 0;

  sized_ptr new_ptr = {.ptr = (void *) ptr, .blackhole = hole};
  return new_ptr;

}

sized_ptr dec(sized_ptr i){
  int *ptr = malloc(sizeof(int));
  int *hole = malloc(sizeof(int));

  if(*i.blackhole) exit(1);

  *ptr = *((int *) i.ptr) - 1;
  *hole = 0;

  sized_ptr new_ptr = {.ptr = (void *) ptr, .blackhole = hole};
  return new_ptr;
}

int isZero(sized_ptr i){
  return *((int *) i.ptr) == 0;
}

sized_ptr mkClos(raw_fun f, int numArgs, ...){
  clos *c = malloc(sizeof(clos));
  int *hole = malloc(sizeof(int));
  va_list l;

  c->fun = f;
  c->numArgs = numArgs + 1;
  c->args = malloc(sizeof(sized_ptr) * (numArgs + 1));
  *hole = 0;

  va_start(l, numArgs);
  for(int i = 0; i < numArgs; ++i)
    c->args[i] = va_arg(l, sized_ptr);
  sized_ptr new_ptr = {.ptr = (void *) c, .blackhole = hole};
  return new_ptr;
}

sized_ptr fixedPoint(sized_ptr f, size_t i){
  int *hole = malloc(sizeof(int));
  sized_ptr sized_dummy = {.ptr = malloc(i),
                           .blackhole = hole};
  *hole = 1;

  clos *c = (clos *) f.ptr;
  c->args[c->numArgs - 1] = sized_dummy;
  sized_ptr res = c->fun(c->args);

  memcpy(sized_dummy.ptr, res.ptr, i);
  *sized_dummy.blackhole = 0;

  return res;
}

void call(raw_fun f){
  sized_ptr i = f(NULL);
  printf("%d\n", *((int *) i.ptr));
}
