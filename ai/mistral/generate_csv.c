#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <inttypes.h>

int main(int argc, char *argv[]) {
    if (argc != 2) {
        fprintf(stderr, "Usage: %s <number_of_lines>\n", argv[0]);
        return 1;
    }

    int num_lines = atoi(argv[1]);
    if (num_lines <= 0) {
        fprintf(stderr, "Number of lines must be a positive integer.\n");
        return 1;
    }

    // Seed the random number generator
    //srand(time(NULL));
    srand(0); // set the seed to 0 instead of time-based seed as proposed above.

    for (int i = 0; i < num_lines; i++) {
        // Generate a random 8-bit signed integer
        int8_t field1 = (int8_t)(rand() % 256) - 128;

        // Generate three random 64-bit unsigned integers
        uint64_t field2 = ((uint64_t)rand() << 32) | rand();
        uint64_t field3 = ((uint64_t)rand() << 32) | rand();
        uint64_t field4 = ((uint64_t)rand() << 32) | rand();

        // Generate a random boolean value (0 or 1)
        bool field5 = rand() % 2;

        // Print the fields separated by colons
        printf("%" PRId8 ":%" PRIu64 ":%" PRIu64 ":%" PRIu64 ":%d\n", field1, field2, field3, field4, field5);
    }

    return 0;
}
