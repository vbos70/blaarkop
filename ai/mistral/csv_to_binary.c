#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <arpa/inet.h>

#define PACKET_SIZE 512

void write_uint64_t_le(uint8_t *buffer, uint64_t value, int offset) {
    buffer[offset] = value & 0xFF;
    buffer[offset + 1] = (value >> 8) & 0xFF;
    buffer[offset + 2] = (value >> 16) & 0xFF;
    buffer[offset + 3] = (value >> 24) & 0xFF;
    buffer[offset + 4] = (value >> 32) & 0xFF;
    buffer[offset + 5] = (value >> 40) & 0xFF;
    buffer[offset + 6] = (value >> 48) & 0xFF;
    buffer[offset + 7] = (value >> 56) & 0xFF;
}

int main() {
    char line[1024];
    uint8_t packet[PACKET_SIZE];

    // Seed the random number generator
    srand(time(NULL));

    while (fgets(line, sizeof(line), stdin)) {
        // Remove newline character
        line[strcspn(line, "\n")] = '\0';

        // Tokenize the line using ':' as the delimiter
        char *token;
        char *rest = line;

        // Field 1: 8-bit signed integer
        token = strtok_r(rest, ":", &rest);
        int8_t field1 = (int8_t)atoi(token);

        // Field 2: 64-bit unsigned integer
        token = strtok_r(rest, ":", &rest);
        uint64_t field2 = strtoull(token, NULL, 10);

        // Field 3: 64-bit unsigned integer
        token = strtok_r(rest, ":", &rest);
        uint64_t field3 = strtoull(token, NULL, 10);

        // Field 4: 64-bit unsigned integer
        token = strtok_r(rest, ":", &rest);
        uint64_t field4 = strtoull(token, NULL, 10);

        // Field 5: Boolean value (0 or 1)
        token = strtok_r(rest, ":", &rest);
        bool field5 = atoi(token);

        // Fill the packet with random bytes
        for (int i = 0; i < PACKET_SIZE; i++) {
            packet[i] = rand() % 256;
        }

        // Write the fields to the packet at the specified positions
        packet[3] = (uint8_t)field1;
        write_uint64_t_le(packet, field2, 37);
        write_uint64_t_le(packet, field3, 37 + 64);
        write_uint64_t_le(packet, field4, 37 + (2 * 64));

        // Set bit 4 of byte 511 to the boolean value
        if (field5) {
            packet[511] |= (1 << 4);
        } else {
            packet[511] &= ~(1 << 4);
        }

        // Write the packet to stdout
        fwrite(packet, sizeof(uint8_t), PACKET_SIZE, stdout);
    }

    return 0;
}
