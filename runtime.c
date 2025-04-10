#include <stdio.h>

/* Use a C compiler to assemble and link a compiled program with the runtime:
 *   cc runtime.c out.s -o out
 * where out.s is the assembly output of the PL/0 compiler, and cc is a
 * C compiler targeting ARM. */


extern void __pl0_start(void);


void __pl0_print(int param)
{
  printf("%d\n", param);
}


int __pl0_read(void)
{
  int tmp;
  scanf("%d", &tmp);
  return tmp;
}


int main(int argc, char *argv[])
{
  __pl0_start();
}



