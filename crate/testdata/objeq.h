/* Structural equality of two Lean objects, for the Lean-level differential (phase-2 §2.8): the old C export's answer
   against the Rust one's, over rust/rt (or rtcount.c + qrt-count.o). `objeq(a, b)` is 1 when they are equal; else 0,
   after printing on stderr what differs and the path to it, innermost first. Constructors compare tag, fields, and the
   whole scalar area (`m_cs_sz` is the rounded byte size under LEAN_MIMALLOC, and lean.h zeroes the rounding); arrays,
   scalar arrays and strings their sizes and contents. Any other kind is reported as not comparable. */
#ifndef QLEAN_OBJEQ_H
#define QLEAN_OBJEQ_H
#include <lean/lean.h>
#include <stdio.h>
#include <string.h>

static int objeq_no(const char *what, unsigned long x, unsigned long y) {
    fprintf(stderr, "objeq: %s differs: %lu vs %lu\n", what, x, y);
    return 0;
}

static int objeq(lean_object *a, lean_object *b) {
    if (lean_is_scalar(a) || lean_is_scalar(b)) {
        if (a == b) return 1;
        if (lean_is_scalar(a) != lean_is_scalar(b)) return objeq_no("scalar-ness", lean_is_scalar(a), lean_is_scalar(b));
        return objeq_no("boxed scalar", lean_unbox(a), lean_unbox(b));
    }
    if (lean_ptr_tag(a) != lean_ptr_tag(b)) return objeq_no("tag", lean_ptr_tag(a), lean_ptr_tag(b));
    if (lean_is_ctor(a)) {
        unsigned n = lean_ctor_num_objs(a);
        if (n != lean_ctor_num_objs(b)) return objeq_no("ctor field count", n, lean_ctor_num_objs(b));
        if (a->m_cs_sz != b->m_cs_sz) return objeq_no("ctor byte size", a->m_cs_sz, b->m_cs_sz);
        for (unsigned i = 0; i < n; i++)
            if (!objeq(lean_ctor_get(a, i), lean_ctor_get(b, i))) { fprintf(stderr, "  in ctor field %u\n", i); return 0; }
        size_t sc = a->m_cs_sz - sizeof(lean_ctor_object) - sizeof(void *) * n;
        if (memcmp(lean_ctor_scalar_cptr(a), lean_ctor_scalar_cptr(b), sc))
            return objeq_no("ctor scalar bytes (count)", sc, sc);
        return 1;
    }
    switch (lean_ptr_tag(a)) {
    case LeanArray: {
        size_t n = lean_array_size(a);
        if (n != lean_array_size(b)) return objeq_no("array size", n, lean_array_size(b));
        for (size_t i = 0; i < n; i++)
            if (!objeq(lean_array_get_core(a, i), lean_array_get_core(b, i))) { fprintf(stderr, "  in array element %zu\n", i); return 0; }
        return 1;
    }
    case LeanScalarArray: {
        size_t n = lean_sarray_size(a), w = lean_sarray_elem_size(a);
        if (w != lean_sarray_elem_size(b)) return objeq_no("scalar array element size", w, lean_sarray_elem_size(b));
        if (n != lean_sarray_size(b)) return objeq_no("scalar array size", n, lean_sarray_size(b));
        for (size_t i = 0; i < n * w; i++)
            if (lean_sarray_cptr(a)[i] != lean_sarray_cptr(b)[i]) {
                fprintf(stderr, "objeq: scalar array byte %zu differs: %u vs %u\n", i, lean_sarray_cptr(a)[i], lean_sarray_cptr(b)[i]);
                return 0;
            }
        return 1;
    }
    case LeanString:
        if (lean_string_size(a) != lean_string_size(b)) return objeq_no("string byte size", lean_string_size(a), lean_string_size(b));
        if (lean_string_len(a) != lean_string_len(b)) return objeq_no("string length", lean_string_len(a), lean_string_len(b));
        if (memcmp(lean_string_cstr(a), lean_string_cstr(b), lean_string_size(a))) {
            fprintf(stderr, "objeq: strings differ: \"%s\" vs \"%s\"\n", lean_string_cstr(a), lean_string_cstr(b));
            return 0;
        }
        return 1;
    default:
        fprintf(stderr, "objeq: objects of tag %u are not comparable here; extend rust/testdata/objeq.h\n", lean_ptr_tag(a));
        return 0;
    }
}
#endif
