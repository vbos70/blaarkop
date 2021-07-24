#include <stdio.h>

/* Read bytes from stdin and compute a checksum. */
unsigned int compute_CRC(void)
{
  unsigned char crc0;
  unsigned char crc1;
  int b;

  crc0 = 0;
  crc1 = 0;

  while((b = getchar()) != EOF) {
    crc0 += b;
    crc1 += crc0 + b;
  }
  return ((crc0 & 0xFF) << 8) + (crc1 & 0xFF);  
}



/* Main program */
int main()
{
  unsigned int crc;

  crc = compute_CRC();
  printf("%02X %02X\n", (crc >> 8) & 0xFF, crc & 0xFF); 
  return 0;
  
}
