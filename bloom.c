/*******************************************************************************
***
***     Author: Tyler Barrus
***     email:  barrust@gmail.com
***
***     Version: 1.9.0
***
***     License: MIT 2015
***
*******************************************************************************/

#include <stdlib.h>
#include <math.h>           /* pow, exp */
#include <stdio.h>          /* printf */
#include <string.h>         /* strlen */
#include <fcntl.h>          /* O_RDWR */
#include <sys/types.h>      /* */
#include <sys/stat.h>       /* fstat */
#include "bloom.h"


#define CHECK_BIT_CHAR(c, k)  ((c) & (1 << (k)))
#define CHECK_BIT(A, k)       (CHECK_BIT_CHAR(A[((k) / 8)], ((k) % 8)))
// #define set_bit(A,k)          (A[((k) / 8)] |=  (1 << ((k) % 8)))
// #define clear_bit(A,k)        (A[((k) / 8)] &= ~(1 << ((k) % 8)))

/* define some constant magic looking numbers */
#define CHAR_LEN 8
#define LOG_TWO_SQUARED  0.480453013918201388143813800   // 0.4804530143737792968750000
                                                        // 0.4804530143737792968750000
#define LOG_TWO 0.693147180559945286226764000

/* https://graphics.stanford.edu/~seander/bithacks.html#CountBitsSetTable */
#define B2(n) n,     n+1,     n+1,     n+2
#define B4(n) B2(n), B2(n+1), B2(n+1), B2(n+2)
#define B6(n) B4(n), B4(n+1), B4(n+1), B4(n+2)
static const unsigned char bits_set_table[256] = {B6(0), B6(1), B6(1), B6(2)};


/*******************************************************************************
***  PRIVATE FUNCTIONS
*******************************************************************************/
static uint64_t* __default_hash(int num_hashes, const uint8_t *str, const size_t str_len);
static uint64_t __fnv_1a(const uint8_t *key, const size_t key_len, int seed);
static void __calculate_optimal_hashes(BloomFilter *bf);
static void __read_from_file(BloomFilter *bf, FILE *fp, short on_disk, const char *filename);
static void __write_to_file(BloomFilter *bf, FILE *fp, short on_disk);
static void __update_elements_added_on_disk(BloomFilter *bf);
static int __sum_bits_set_char(unsigned char c);
static int __check_if_union_or_intersection_ok(BloomFilter *res, BloomFilter *bf1, BloomFilter *bf2);


int bloom_filter_init_alt(BloomFilter *bf, uint64_t estimated_elements, float false_positive_rate, BloomHashFunction hash_function) {
    if(estimated_elements == 0 || estimated_elements > UINT64_MAX || false_positive_rate <= 0.0 || false_positive_rate >= 1.0) {
        return BLOOM_FAILURE;
    }
    bf->estimated_elements = estimated_elements;
    bf->false_positive_probability = false_positive_rate;
    __calculate_optimal_hashes(bf);
    bf->bloom = (unsigned char*)calloc(bf->bloom_length + 1, sizeof(char)); // pad to ensure no running off the end
    bf->elements_added = 0;
    bloom_filter_set_hash_function(bf, hash_function);
    return BLOOM_SUCCESS;
}

void bloom_filter_set_hash_function(BloomFilter *bf, BloomHashFunction hash_function) {
    bf->hash_function = (hash_function == NULL) ? __default_hash : hash_function;
}

int bloom_filter_destroy(BloomFilter *bf) {
    free(bf->bloom);
    bf->bloom = NULL;
    bf->elements_added = 0;
    bf->estimated_elements = 0;
    bf->false_positive_probability = 0;
    bf->number_hashes = 0;
    bf->number_bits = 0;
    bf->hash_function = NULL;
    return BLOOM_SUCCESS;
}

int bloom_filter_clear(BloomFilter *bf) {
    for (unsigned long i = 0; i < bf->bloom_length; ++i) {
        bf->bloom[i] = 0;
    }
    bf->elements_added = 0;
    __update_elements_added_on_disk(bf);
    return BLOOM_SUCCESS;
}

void bloom_filter_stats(BloomFilter *bf) {
    uint64_t size_on_disk = bloom_filter_export_size(bf);

    printf("BloomFilter\n\
    bits: %" PRIu64 "\n\
    estimated elements: %" PRIu64 "\n\
    number hashes: %d\n\
    max false positive rate: %f\n\
    bloom length (8 bits): %ld\n\
    elements added: %" PRIu64 "\n\
    estimated elements added: %" PRIu64 "\n\
    current false positive rate: %f\n\
    export size (bytes): %" PRIu64 "\n\
    number bits set: %" PRIu64 "\n",
    bf->number_bits, bf->estimated_elements, bf->number_hashes,
    bf->false_positive_probability, bf->bloom_length, bf->elements_added,
    bloom_filter_estimate_elements(bf),
    bloom_filter_current_false_positive_rate(bf), size_on_disk,
    bloom_filter_count_set_bits(bf));
}

int bloom_filter_add_string(BloomFilter *bf, const char *str) {
    return bloom_filter_add_uint8_str(bf, (const uint8_t *) str, strlen(str));
}

int bloom_filter_add_uint8_str(BloomFilter *bf, const uint8_t *str, const size_t str_len) {
    uint64_t *hashes = bloom_filter_calculate_hashes(bf, str, str_len, bf->number_hashes);
    int res = bloom_filter_add_string_alt(bf, hashes, bf->number_hashes);
    free(hashes);
    return res;
}

int bloom_filter_check_string(BloomFilter *bf, const char *str) {
    return bloom_filter_check_uint8_str(bf, (const uint8_t *) str, strlen(str));
}

int bloom_filter_check_uint8_str(BloomFilter *bf, const uint8_t *str, const size_t str_len) {
    uint64_t *hashes = bloom_filter_calculate_hashes(bf, str, str_len, bf->number_hashes);
    int res = bloom_filter_check_string_alt(bf, hashes, bf->number_hashes);
    free(hashes);
    return res;
}

uint64_t* bloom_filter_calculate_hashes(BloomFilter *bf, const uint8_t *str, const size_t str_len, unsigned int number_hashes) {
    return bf->hash_function(number_hashes, str, str_len);
}

/* Add a string to a bloom filter using the defined hashes */
int bloom_filter_add_string_alt(BloomFilter *bf, uint64_t *hashes, unsigned int number_hashes_passed) {
    if (number_hashes_passed < bf->number_hashes) {
        fprintf(stderr, "Error: not enough hashes passed in to correctly check!\n");
        return BLOOM_FAILURE;
    }

    for (unsigned int i = 0; i < bf->number_hashes; ++i) {
        unsigned long idx = (hashes[i] % bf->number_bits) / 8;
        int bit = (hashes[i] % bf->number_bits) % 8;

        bf->bloom[idx] |= (1 << bit); // set the bit
    }

    bf->elements_added++;
    __update_elements_added_on_disk(bf);
    return BLOOM_SUCCESS;
}

/* Check if a string is in the bloom filter using the passed hashes */
int bloom_filter_check_string_alt(BloomFilter *bf, uint64_t *hashes, unsigned int number_hashes_passed) {
    if (number_hashes_passed < bf->number_hashes) {
        fprintf(stderr, "Error: not enough hashes passed in to correctly check!\n");
        return BLOOM_FAILURE;
    }

    unsigned int i;
    int r = BLOOM_SUCCESS;
    for (i = 0; i < bf->number_hashes; ++i) {
        int tmp_check = CHECK_BIT(bf->bloom, (hashes[i] % bf->number_bits));
        if (tmp_check == 0) {
            r = BLOOM_FAILURE;
            break; // no need to continue checking
        }
    }
    return r;
}

float bloom_filter_current_false_positive_rate(BloomFilter *bf) {
    int num = bf->number_hashes * bf->elements_added;
    double d = -num / (float) bf->number_bits;
    double e = exp(d);
    return pow((1 - e), bf->number_hashes);
}

uint64_t bloom_filter_export_size(BloomFilter *bf) {
    return (uint64_t)(bf->bloom_length * sizeof(unsigned char)) + (2 * sizeof(uint64_t)) + sizeof(float);
}

uint64_t bloom_filter_count_set_bits(BloomFilter *bf) {
    uint64_t i, res = 0;
    for (i = 0; i < bf->bloom_length; ++i) {
        res += __sum_bits_set_char(bf->bloom[i]);
    }
    return res;
}

uint64_t bloom_filter_estimate_elements(BloomFilter *bf) {
    return bloom_filter_estimate_elements_by_values(bf->number_bits, bloom_filter_count_set_bits(bf), bf->number_hashes);
}

uint64_t bloom_filter_estimate_elements_by_values(uint64_t m, uint64_t X, int k) {
    /* m = number bits; X = count of flipped bits; k = number hashes */
    double log_n = log(1 - ((double) X / (double) m));
    return (uint64_t)-(((double) m / k) * log_n);
}

int bloom_filter_union(BloomFilter *res, BloomFilter *bf1, BloomFilter *bf2) {
    // Ensure the bloom filters can be unioned
    if (__check_if_union_or_intersection_ok(res, bf1, bf2) == BLOOM_FAILURE) {
        return BLOOM_FAILURE;
    }
    uint64_t i;
    for (i = 0; i < bf1->bloom_length; ++i) {
        res->bloom[i] = bf1->bloom[i] | bf2->bloom[i];
    }
    bloom_filter_set_elements_to_estimated(res);
    return BLOOM_SUCCESS;
}

uint64_t bloom_filter_count_union_bits_set(BloomFilter *bf1, BloomFilter *bf2) {
    // Ensure the bloom filters can be unioned
    if (__check_if_union_or_intersection_ok(bf1, bf1, bf2) == BLOOM_FAILURE) {  // use bf1 as res
        return BLOOM_FAILURE;
    }
    uint64_t i, res = 0;
    for (i = 0; i < bf1->bloom_length; ++i) {
        res += __sum_bits_set_char(bf1->bloom[i] | bf2->bloom[i]);
    }
    return res;
}

int bloom_filter_intersect(BloomFilter *res, BloomFilter *bf1, BloomFilter *bf2) {
    // Ensure the bloom filters can be used in an intersection
    if (__check_if_union_or_intersection_ok(res, bf1, bf2) == BLOOM_FAILURE) {
        return BLOOM_FAILURE;
    }
    uint64_t i;
    for (i = 0; i < bf1->bloom_length; ++i) {
        res->bloom[i] = bf1->bloom[i] & bf2->bloom[i];
    }
    bloom_filter_set_elements_to_estimated(res);
    return BLOOM_SUCCESS;
}

void bloom_filter_set_elements_to_estimated(BloomFilter *bf) {
    bf->elements_added = bloom_filter_estimate_elements(bf);
    __update_elements_added_on_disk(bf);
}

uint64_t bloom_filter_count_intersection_bits_set(BloomFilter *bf1, BloomFilter *bf2) {
    // Ensure the bloom filters can be used in an intersection
    if (__check_if_union_or_intersection_ok(bf1, bf1, bf2) == BLOOM_FAILURE) {  // use bf1 as res
        return BLOOM_FAILURE;
    }
    uint64_t i, res = 0;
    for (i = 0; i < bf1->bloom_length; ++i) {
        res += __sum_bits_set_char(bf1->bloom[i] & bf2->bloom[i]);
    }
    return res;
}

float bloom_filter_jaccard_index(BloomFilter *bf1, BloomFilter *bf2) {
    // Ensure the bloom filters can be used in an intersection and union
    if (__check_if_union_or_intersection_ok(bf1, bf1, bf2) == BLOOM_FAILURE) {  // use bf1 as res
        return (float)BLOOM_FAILURE;
    }
    float set_union_bits = (float)bloom_filter_count_union_bits_set(bf1, bf2);
    if (set_union_bits == 0) {  // check for divide by 0 error
        return 1.0; // they must be both empty for this to occur and are therefore the same
    }
    return (float)bloom_filter_count_intersection_bits_set(bf1, bf2) / set_union_bits;
}

/*******************************************************************************
*    PRIVATE FUNCTIONS
*******************************************************************************/
static void __calculate_optimal_hashes(BloomFilter *bf) {
    // calc optimized values
    long n = bf->estimated_elements;
    float p = bf->false_positive_probability;
    uint64_t m = ceil((-n * logl(p)) / LOG_TWO_SQUARED);  // AKA pow(log(2), 2);
    unsigned int k = round(LOG_TWO * m / n);             // AKA log(2.0);
    // set paramenters
    bf->number_hashes = k; // should check to make sure it is at least 1...
    bf->number_bits = m;
    long num_pos = ceil(m / (CHAR_LEN * 1.0));
    bf->bloom_length = num_pos;
}

static int __sum_bits_set_char(unsigned char c) {
    return bits_set_table[c];
}

static int __check_if_union_or_intersection_ok(BloomFilter *res, BloomFilter *bf1, BloomFilter *bf2) {
    if (res->number_hashes != bf1->number_hashes || bf1->number_hashes != bf2->number_hashes) {
        return BLOOM_FAILURE;
    } else if (res->number_bits != bf1->number_bits || bf1->number_bits != bf2->number_bits) {
        return BLOOM_FAILURE;
    } else if (res->hash_function != bf1->hash_function || bf1->hash_function != bf2->hash_function) {
        return BLOOM_FAILURE;
    }
    return BLOOM_SUCCESS;
}

/* NOTE: The caller will free the results */
static uint64_t* __default_hash(int num_hashes, const uint8_t *str, const size_t str_len) {
    uint64_t *results = (uint64_t*)calloc(num_hashes, sizeof(uint64_t));
    int i;
    for (i = 0; i < num_hashes; ++i) {
        results[i] = __fnv_1a(str, str_len, i);
    }
    return results;
}

static uint64_t __fnv_1a(const uint8_t *key, const size_t len, int seed) {
    // FNV-1a hash (http://www.isthe.com/chongo/tech/comp/fnv/)
    size_t i;
    uint64_t h = 14695981039346656037ULL + (31 * seed); // FNV_OFFSET 64 bit with magic number seed
    for (i = 0; i < len; ++i){
            h = h ^ (unsigned char) key[i];
            h = h * 1099511628211ULL; // FNV_PRIME 64 bit
    }
    return h;
}
