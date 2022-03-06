#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {

  double d = atof(argv[1]);

  double n;
  long long a; // 64 bit machine
  double b;

  // go_s17J :: Double# -> Int# -> Double# -> Double#
  for (n = 1, a = 0, b = 0;
       n <= d;
       b+=n, n++, a++);

  if (d > 0) {
    printf("%f\n", b / a);
  }
  else {
    printf("0.0\n");
  }
      
  return 0;
}
