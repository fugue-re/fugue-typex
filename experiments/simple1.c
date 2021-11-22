// gcc -m32 -no-pie -fno-pic -O0 -o simple1 simple1.c

#include <stdio.h>

struct simple_t {
  int a;
  char *b;
};

void run2(struct simple_t *v) {
  puts(v->b);
}

void run1(int a, char *b) {
  struct simple_t s = {
    .a = a,
    .b = b,
  };

  if (a > 1) {
    puts(s.b);
  } else {
    run2(&s);
  }
}

int main(int argc, char **argv) {
  run1(argc, argv[argc-1]);
  return 0;
}
