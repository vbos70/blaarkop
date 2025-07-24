#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <inttypes.h>

#define PACKET_SIZE 512

uint64_t read_uint64_t_le(const uint8_t *buffer, int offset) {
    uint64_t value = 0;
    for (int i = 0; i < 8; i++) {
        value |= (uint64_t)buffer[offset + i] << (8 * i);
    }
    return value;
}

int main() {
    uint8_t packet[PACKET_SIZE];

    while (fread(packet, sizeof(uint8_t), PACKET_SIZE, stdin) == PACKET_SIZE) {
        // Extract Field 1: 8-bit signed integer at byte position 3
        int8_t field1 = (int8_t)packet[3];

        // Extract Field 2: 64-bit unsigned integer at byte position 37
        uint64_t field2 = read_uint64_t_le(packet, 37);

        // Extract Field 3: 64-bit unsigned integer at byte position 37 + 64
        uint64_t field3 = read_uint64_t_le(packet, 37 + 64);

        // Extract Field 4: 64-bit unsigned integer at byte position 37 + (2 * 64)
        uint64_t field4 = read_uint64_t_le(packet, 37 + (2 * 64));

        // Extract Field 5: Boolean value (bit 4 of byte 511)
        bool field5 = (packet[511] >> 4) & 1;

        // Write the fields to stdout separated by colons
        printf("%" PRId8 ":%" PRIu64 ":%" PRIu64 ":%" PRIu64 ":%u\n", field1, field2, field3, field4, field5);
    }

    return 0;
}
