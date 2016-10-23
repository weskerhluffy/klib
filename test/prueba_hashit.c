#include <stdlib.h>
#include <stdio.h>

/*!
 @header

 Generic hash table library.
 */

#include <stdlib.h>
#include <string.h>
#include <limits.h>
#include <assert.h>

typedef unsigned int khint32_t;

typedef unsigned long long khint64_t;
typedef khint32_t khint_t;
typedef khint_t khiter_t;
static const double __ac_HASH_UPPER = 0.77;
static inline khint_t __ac_X31_hash_string(const char *s) {
	khint_t h = (khint_t) *s;
	if (h)
		for (++s; *s; ++s)
			h = (h << 5) - h + (khint_t) *s;
	return h;
}
static inline khint_t __ac_Wang_hash(khint_t key) {
	key += ~(key << 15);
	key ^= (key >> 10);
	key += (key << 3);
	key ^= (key >> 6);
	key += ~(key << 11);
	key ^= (key >> 16);
	return key;
}
typedef const char *kh_cstr_t;
typedef struct kh_caca_s {
	khint_t n_buckets, size, n_occupied, upper_bound;
	khint32_t *flags;
	khint32_t *keys;
	int *vals;
} kh_caca_t;

#define kh_key(h, x) ((h)->keys[x])
#define kh_val(h, x) ((h)->vals[x])
#define kh_value(h, x) ((h)->vals[x])
#define kh_begin(h) (khint_t)(0)
#define kh_end(h) ((h)->n_buckets)
#define kh_size(h) ((h)->size)
#define kh_exist(h, x) (!__ac_iseither((h)->flags, (x)))

#define __ac_isempty(flag, i) ((flag[i>>4]>>((i&0xfU)<<1))&2)
#define __ac_isdel(flag, i) ((flag[i>>4]>>((i&0xfU)<<1))&1)
#define __ac_iseither(flag, i) ((flag[i>>4]>>((i&0xfU)<<1))&3)
#define __ac_set_isdel_false(flag, i) (flag[i>>4]&=~(1ul<<((i&0xfU)<<1)))
#define __ac_set_isempty_false(flag, i) (flag[i>>4]&=~(2ul<<((i&0xfU)<<1)))
#define __ac_set_isboth_false(flag, i) (flag[i>>4]&=~(3ul<<((i&0xfU)<<1)))
#define __ac_set_isdel_true(flag, i) (flag[i>>4]|=1ul<<((i&0xfU)<<1))
#define __ac_fsize(m) ((m) < 16? 1 : (m)>>4)

static inline __attribute__ ((__unused__)) kh_caca_t *kh_init_caca(void) {
	return (kh_caca_t*) calloc(1, sizeof(kh_caca_t));
}
static inline __attribute__ ((__unused__)) void kh_destroy_caca(kh_caca_t *h) {
	if (h) {
		free((void *) h->keys);
		free(h->flags);
		free((void *) h->vals);
		free(h);
	}
}
static inline __attribute__ ((__unused__)) void kh_clear_caca(kh_caca_t *h) {
	if (h && h->flags) {
		__builtin___memset_chk(h->flags, 0xaa,
				((h->n_buckets) < 16 ? 1 : (h->n_buckets) >> 4)
						* sizeof(khint32_t),
				__builtin_object_size(h->flags, 0));
		h->size = h->n_occupied = 0;
	}
}
static inline __attribute__ ((__unused__)) khint_t kh_get_caca(
		const kh_caca_t *h, khint32_t key) {
	if (h->n_buckets) {
		khint_t k, i, last, mask, step = 0;
		mask = h->n_buckets - 1;
		k = (khint32_t) (key);
		i = k & mask;
		last = i;
		while (!((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 2)
				&& (((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 1)
						|| !((h->keys[i]) == (key)))) {
			i = (i + (++step)) & mask;
			if (i == last)
				return h->n_buckets;
		}
		return ((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 3) ? h->n_buckets : i;
	} else
		return 0;
}
static inline __attribute__ ((__unused__)) int kh_resize_caca(kh_caca_t *h,
		khint_t new_n_buckets) {
	khint32_t *new_flags = 0;
	khint_t j = 1;
	{
		(--(new_n_buckets), (new_n_buckets) |= (new_n_buckets) >> 1, (new_n_buckets) |=
				(new_n_buckets) >> 2, (new_n_buckets) |= (new_n_buckets) >> 4, (new_n_buckets) |=
				(new_n_buckets) >> 8, (new_n_buckets) |= (new_n_buckets) >> 16, ++(new_n_buckets));
		if (new_n_buckets < 4)
			new_n_buckets = 4;
		if (h->size >= (khint_t) (new_n_buckets * __ac_HASH_UPPER + 0.5))
			j = 0;
		else {
			new_flags = (khint32_t*) malloc(
					((new_n_buckets) < 16 ? 1 : (new_n_buckets) >> 4)
							* sizeof(khint32_t));
			if (!new_flags)
				return -1;
			__builtin___memset_chk(new_flags, 0xaa,
					((new_n_buckets) < 16 ? 1 : (new_n_buckets) >> 4)
							* sizeof(khint32_t),
					__builtin_object_size(new_flags, 0));
			if (h->n_buckets < new_n_buckets) {
				khint32_t *new_keys = (khint32_t*) realloc((void *) h->keys,
						new_n_buckets * sizeof(khint32_t));
				if (!new_keys) {
					free(new_flags);
					return -1;
				}
				h->keys = new_keys;
				if (1) {
					int *new_vals = (int*) realloc((void *) h->vals,
							new_n_buckets * sizeof(int));
					if (!new_vals) {
						free(new_flags);
						return -1;
					}
					h->vals = new_vals;
				}
			}
		}
	}
	if (j) {
		for (j = 0; j != h->n_buckets; ++j) {
			if (((h->flags[j >> 4] >> ((j & 0xfU) << 1)) & 3) == 0) {
				khint32_t key = h->keys[j];
				int val;
				khint_t new_mask;
				new_mask = new_n_buckets - 1;
				if (1)
					val = h->vals[j];
				(h->flags[j >> 4] |= 1ul << ((j & 0xfU) << 1));
				while (1) {
					khint_t k, i, step = 0;
					k = (khint32_t) (key);
					i = k & new_mask;
					while (!((new_flags[i >> 4] >> ((i & 0xfU) << 1)) & 2))
						i = (i + (++step)) & new_mask;
					(new_flags[i >> 4] &= ~(2ul << ((i & 0xfU) << 1)));
					if (i < h->n_buckets
							&& ((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 3)
									== 0) {
						{
							khint32_t tmp = h->keys[i];
							h->keys[i] = key;
							key = tmp;
						}
						if (1) {
							int tmp = h->vals[i];
							h->vals[i] = val;
							val = tmp;
						}
						(h->flags[i >> 4] |= 1ul << ((i & 0xfU) << 1));
					} else {
						h->keys[i] = key;
						if (1)
							h->vals[i] = val;
						break;
					}
				}
			}
		}
		if (h->n_buckets > new_n_buckets) {
			h->keys = (khint32_t*) realloc((void *) h->keys,
					new_n_buckets * sizeof(khint32_t));
			if (1)
				h->vals = (int*) realloc((void *) h->vals,
						new_n_buckets * sizeof(int));
		}
		free(h->flags);
		h->flags = new_flags;
		h->n_buckets = new_n_buckets;
		h->n_occupied = h->size;
		h->upper_bound = (khint_t) (h->n_buckets * __ac_HASH_UPPER + 0.5);
	}
	return 0;
}
static inline __attribute__ ((__unused__)) khint_t kh_put_caca(kh_caca_t *h,
		khint32_t key, int *ret) {
	khint_t x;
	if (h->n_occupied >= h->upper_bound) {
		if (h->n_buckets > (h->size << 1)) {
			if (kh_resize_caca(h, h->n_buckets - 1) < 0) {
				*ret = -1;
				return h->n_buckets;
			}
		} else if (kh_resize_caca(h, h->n_buckets + 1) < 0) {
			*ret = -1;
			return h->n_buckets;
		}
	}
	{
		khint_t k, i, site, last, mask = h->n_buckets - 1, step = 0;
		x = site = h->n_buckets;
		k = (khint32_t) (key);
		i = k & mask;
		if (((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 2))
			x = i;
		else {
			last = i;
			while (!((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 2)
					&& (((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 1)
							|| !((h->keys[i]) == (key)))) {
				if (((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 1))
					site = i;
				i = (i + (++step)) & mask;
				if (i == last) {
					x = site;
					break;
				}
			}
			if (x == h->n_buckets) {
				if (((h->flags[i >> 4] >> ((i & 0xfU) << 1)) & 2)
						&& site != h->n_buckets)
					x = site;
				else
					x = i;
			}
		}
	}
	if (((h->flags[x >> 4] >> ((x & 0xfU) << 1)) & 2)) {
		h->keys[x] = key;
		(h->flags[x >> 4] &= ~(3ul << ((x & 0xfU) << 1)));
		++h->size;
		++h->n_occupied;
		*ret = 1;
	} else if (((h->flags[x >> 4] >> ((x & 0xfU) << 1)) & 1)) {
		h->keys[x] = key;
		(h->flags[x >> 4] &= ~(3ul << ((x & 0xfU) << 1)));
		++h->size;
		*ret = 2;
	} else
		*ret = 0;
	return x;
}
static inline __attribute__ ((__unused__)) void kh_del_caca(kh_caca_t *h,
		khint_t x) {
	if (x != h->n_buckets && !((h->flags[x >> 4] >> ((x & 0xfU) << 1)) & 3)) {
		(h->flags[x >> 4] |= 1ul << ((x & 0xfU) << 1));
		--h->size;
	}
}

/*
 An example:

 #include "khash.h"
 KHASH_MAP_INIT_INT(32, char)
 int main() {
 int ret, is_missing;
 khiter_t k;
 khash_t(32) *h = kh_init(32);
 k = kh_put(32, h, 5, &ret);
 kh_value(h, k) = 10;
 k = kh_get(32, h, 10);
 is_missing = (k == kh_end(h));
 k = kh_get(32, h, 5);
 kh_del(32, h, k);
 for (k = kh_begin(h); k != kh_end(h); ++k)
 if (kh_exist(h, k)) kh_value(h, k) = 1;
 kh_destroy(32, h);
 return 0;
 }
 */

int main() {
	int ret, is_missing = 0, cagada = 0;
	khiter_t k;
	kh_caca_t * h = kh_init_caca();

	for (int i = -25000; i < 25000; i++) {
		k = kh_put_caca(h, i, &ret);
		kh_value(h, k)= 1;
		if (!i) {
			printf("el valor 0 tiene %u en slot %u\n", k, kh_value(h, k));
		}
		cagada++;
	}

	for (int i = -25000; i < 25000; i++) {
		k = kh_put_caca(h, i, &ret);
		kh_value(h, k)+= 1;
	}

	for (k = kh_begin(h) ; k != kh_end(h); ++k)
		if (kh_exist(h, k)) {
			is_missing++;
			assert(kh_value(h, k) == 2);
		}

	printf("ismisis es %u\n", is_missing);
	assert(is_missing == cagada);
	kh_destroy_caca(h);
	return 0;
}
