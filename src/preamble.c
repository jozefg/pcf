#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include <string.h>

#define EMPTY {.blackhole = NULL, .ptr = NULL}
#define INT_SIZE sizeof(int)
#define CLOS_SIZE sizeof(clos)

typedef struct {
  void *ptr;
  int *blackhole;
} tagged_ptr;

typedef tagged_ptr (*raw_fun)(tagged_ptr *);

typedef struct {
  raw_fun fun;
  int numArgs;
  tagged_ptr *args;
} clos;

tagged_ptr apply(tagged_ptr fun, tagged_ptr arg){
  if(*fun.blackhole || *arg.blackhole) exit(1);

  clos *c = (clos *) fun.ptr;
  c->args[c->numArgs - 1] = arg;
  return c->fun(c->args);
}

tagged_ptr mkZero(){
  int *ptr = malloc(sizeof(int));
  int *hole = malloc(sizeof(int));

    *ptr = 0;
  *hole = 0;

  tagged_ptr new_ptr = {.ptr = (void *) ptr, .blackhole = hole};
  return new_ptr;
}

tagged_ptr inc(tagged_ptr i){
  int *ptr = malloc(sizeof(int));
  int *hole = malloc(sizeof(int));

  if(*i.blackhole) exit(1);

  *ptr = *((int *) i.ptr) + 1;
  *hole = 0;

  tagged_ptr new_ptr = {.ptr = (void *) ptr, .blackhole = hole};
  return new_ptr;

}

tagged_ptr dec(tagged_ptr i){
  int *ptr = malloc(sizeof(int));
  int *hole = malloc(sizeof(int));

  if(*i.blackhole) exit(1);

  *ptr = *((int *) i.ptr) - 1;
  *hole = 0;

  tagged_ptr new_ptr = {.ptr = (void *) ptr, .blackhole = hole};
  return new_ptr;
}

int isZero(tagged_ptr i){
  return *((int *) i.ptr) == 0;
}

tagged_ptr mkClos(raw_fun f, int numArgs, ...){
  clos *c = malloc(sizeof(clos));
  int *hole = malloc(sizeof(int));
  va_list l;

  c->fun = f;
  c->numArgs = numArgs + 1;
  c->args = malloc(sizeof(tagged_ptr) * (numArgs + 1));
  *hole = 0;

  va_start(l, numArgs);
  for(int i = 0; i < numArgs; ++i)
    c->args[i] = va_arg(l, tagged_ptr);
  tagged_ptr new_ptr = {.ptr = (void *) c, .blackhole = hole};
  return new_ptr;
}

tagged_ptr fixedPoint(tagged_ptr f, size_t i){
  int *hole = malloc(sizeof(int));
  tagged_ptr sized_dummy = {.ptr = malloc(i),
                           .blackhole = hole};
  *hole = 1;

  clos *c = (clos *) f.ptr;
  c->args[c->numArgs - 1] = sized_dummy;
  tagged_ptr res = c->fun(c->args);

  if(res.blackhole) exit(1);

  memcpy(sized_dummy.ptr, res.ptr, i);
  *sized_dummy.blackhole = 0;

  return res;
}

void call(raw_fun f){
  tagged_ptr i = f(NULL);
  printf("%d\n", *((int *) i.ptr));
}
