#include "error.h"
#include "import.h"
#include "inline.h"

#include <stddef.h>
#include <string.h>

static inline unsigned *
begin_archive_vector (kissat *solver, archive_vector *archive_vector) {
#ifdef COMPACT
  return BEGIN_STACK (solver->archive_vectors.stack) +
         archive_vector->offset;
#else
  (void) solver;
  return archive_vector->begin;
#endif
}

static inline unsigned *
end_archive_vector (kissat *solver, archive_vector *archive_vector) {
#ifdef COMPACT
  return begin_archive_vector (solver, archive_vector) +
         archive_vector->size;
#else
  (void) solver;
  return archive_vector->end;
#endif
}

void check_archive_watches (kissat *solver) {
#if defined(CHECK_VECTORS)
  volatile unsigned a;
  for (int i = 0; i < 2 * solver->max_var; i++) {
    archive_watches watches = solver->archive_watches[i];
    unsigned *begin = begin_archive_vector (solver, &watches);
    unsigned *end = end_archive_vector (solver, &watches);
    unsigned *current = begin;
    while (current != end) {
      a = *current;
      current += 1;
    }
  }
  (void) a;
#else
  (void) solver;
#endif
}

static inline size_t actual_bytes_of_archive_clause (archive_clause *c) {
  int const *p = END_LITS (c);
  return kissat_align_ward ((char *) p - (char *) c);
}

static inline archive_clause *next_archive_clause (archive_clause *c) {
  word bytes = actual_bytes_of_archive_clause (c);
  return (archive_clause *) ((char *) c + bytes);
}

static inline size_t bytes_of_archive_clause (unsigned size) {
  const size_t res = sizeof (archive_clause) + (size - 3) * sizeof (int);
  return kissat_align_ward (res);
}

static reference allocate_archived_clause (kissat *solver, size_t size) {
  assert (size <= UINT_MAX);
  const size_t res = SIZE_STACK (solver->archive);
  assert (res <= MAX_REF);
  const size_t bytes = bytes_of_archive_clause (size);
  assert (kissat_aligned_word (bytes));
  const size_t needed = bytes / sizeof (ward);
  assert (needed <= UINT_MAX);
  size_t capacity = CAPACITY_STACK (solver->archive);
  assert (kissat_is_power_of_two (MAX_ARENA));
  assert (capacity <= MAX_ARENA);
  size_t available = capacity - res;
  if (needed > available) {
    do {
      assert (kissat_is_zero_or_power_of_two (capacity));
      if (capacity == MAX_ARENA)
        kissat_fatal ("maximum archive capacity "
                      "of 2^%u %zu-byte-words %s exhausted"
#ifdef COMPACT
                      " (consider a configuration without '--compact')"
#endif
                      ,
                      LD_MAX_ARENA, sizeof (ward),
                      FORMAT_BYTES (MAX_ARENA * sizeof (ward)));
      kissat_stack_enlarge (solver, (chars *) &solver->archive,
                            sizeof (ward));
      capacity = CAPACITY_STACK (solver->archive);
      available = capacity - res;
    } while (needed > available);
    assert (capacity <= MAX_ARENA);
  }
  solver->archive.end += needed;
  assert (SIZE_STACK (solver->archive) != 0);
  return (reference) res;
}

static inline archive_clause *
unchecked_dereference_archive_clause (kissat *solver, reference ref) {
  return (archive_clause *) &PEEK_STACK (solver->archive, ref);
}

#ifndef NDEBUG
static bool clause_in_archive (const kissat *solver,
                               const archive_clause *c) {
  if (!kissat_aligned_pointer (c))
    return false;
  const char *p = (char *) c;
  const char *begin = (char *) BEGIN_STACK (solver->archive);
  const char *end = (char *) END_STACK (solver->archive);
  if (p < begin)
    return false;
  const size_t bytes = bytes_of_archive_clause (c->size);
  if (end < p + bytes)
    return false;
  return true;
}
#endif

static inline reference reference_archive_clause (kissat *solver,
                                                  const archive_clause *c) {
#ifndef NDEBUG
  assert (clause_in_archive (solver, c));
#endif
  return (ward *) c - BEGIN_STACK (solver->archive);
}

static int lit2idx (int lit) {
  if (lit < 0) {
    return -lit * 2 - 2;
  } else {
    return lit * 2 - 1;
  }
}

static inline archive_watch archive_blocking_archive_watch (int lit) {
  archive_watch res;
  res.blocking.lit = lit;
  res.blocking.binary = false;
  assert (!res.type.binary);
  return res;
}

static inline archive_watch archive_large_archive_watch (reference ref) {
  archive_watch res;
  res.large.ref = ref;
  res.large.binary = false;
  assert (!res.type.binary);
  return res;
}

static inline void add_archive_usable (kissat *solver, size_t inc) {
  assert (MAX_SECTOR - inc >= solver->archive_vectors.usable);
  solver->archive_vectors.usable += inc;
}

static inline void dec_archive_usable (kissat *solver) {
  assert (solver->archive_vectors.usable > 0);
  solver->archive_vectors.usable--;
}

static inline size_t
size_archive_vector (const archive_vector *archive_vector) {
#ifdef COMPACT
  return archive_vector->size;
#else
  return archive_vector->end - archive_vector->begin;
#endif
}

#ifndef COMPACT

static void
fix_archive_vector_pointers_after_moving_stack (kissat *solver,
                                                ptrdiff_t moved) {
#ifdef LOGGING
  uint64_t bytes = moved < 0 ? -moved : moved;
  LOG ("fixing begin and end pointers of all watches "
       "since the global watches stack has been moved by %s",
       FORMAT_BYTES (bytes));
#endif
  struct archive_vector *begin_watches = solver->archive_watches;
  struct archive_vector *end_watches = begin_watches + 2 * solver->max_var;
  for (struct archive_vector *p = begin_watches; p != end_watches; p++) {

#define FIX_POINTER(PTR) \
  do { \
    char *old_char_ptr_value = (char *) (PTR); \
    if (!old_char_ptr_value) \
      break; \
    char *new_char_ptr_value = old_char_ptr_value + moved; \
    unsigned *new_unsigned_ptr_value = (unsigned *) new_char_ptr_value; \
    (PTR) = new_unsigned_ptr_value; \
  } while (0)

    FIX_POINTER (p->begin);
    FIX_POINTER (p->end);
  }
}

#endif

#define archive_LITS (2 * solver->max_var)

#define all_archive_idx(LIT) \
  unsigned LIT = 0, LIT##_END = archive_LITS; \
  LIT != LIT##_END; \
  ++LIT

#ifdef CHECK_VECTORS

void check_archive_vector (kissat *solver, archive_vector *archive_vector) {
  const unsigned *const begin =
      begin_archive_vector (solver, archive_vector);
  const unsigned *const end = end_archive_vector (solver, archive_vector);
  if (!solver->transitive_reducing)
    for (const unsigned *p = begin; p != end; p++)
      assert (*p != INVALID_VECTOR_ELEMENT);
#ifdef NDEBUG
  (void) solver;
#endif
}

void check_archive_vectors (kissat *solver) {
  if (solver->transitive_reducing)
    return;
  for (all_archive_idx (idx)) {
    archive_vector *archive_vector = &solver->archive_watches[idx];
    check_archive_vector (solver, archive_vector);
  }
  archive_vectors *archive_vectors = &solver->archive_vectors;
  unsigneds *stack = &archive_vectors->stack;
  const unsigned *const begin = BEGIN_STACK (*stack);
  const unsigned *const end = END_STACK (*stack);
  if (begin == end)
    return;
  size_t invalid = 0;
  for (const unsigned *p = begin + 1; p != end; p++)
    if (*p == INVALID_VECTOR_ELEMENT)
      invalid++;
  assert (invalid == solver->archive_vectors.usable);
}
#else
#define check_archive_vectors(...) \
  do { \
  } while (0)
#endif

#if defined(LOGGING) || defined(TEST_VECTOR)

static inline size_t
offset_archive_vector (kissat *solver, archive_vector *archive_vector) {
#ifdef COMPACT
  (void) solver;
  return archive_vector->offset;
#else
  unsigned *begin_archive_vector = archive_vector->begin;
  unsigned *begin_stack = BEGIN_STACK (solver->archive_vectors.stack);
  return begin_archive_vector ? begin_archive_vector - begin_stack : 0;
#endif
}

#endif

unsigned *enlarge_archive_vector (kissat *solver,
                                  archive_vector *archive_vector) {
  unsigneds *stack = &solver->archive_vectors.stack;
  const size_t old_archive_vector_size =
      size_archive_vector (archive_vector);
#ifdef LOGGING
  const size_t old_offset = offset_archive_vector (solver, archive_vector);
  LOG2 ("enlarging archive_vector %zu[%zu] at %p", old_offset,
        old_archive_vector_size, (void *) archive_vector);
#endif
  assert (old_archive_vector_size < MAX_VECTORS / 2);
  const size_t new_archive_vector_size =
      old_archive_vector_size ? 2 * old_archive_vector_size : 1;
  size_t old_stack_size = SIZE_STACK (*stack);
  size_t capacity = CAPACITY_STACK (*stack);
  assert (kissat_is_power_of_two (MAX_VECTORS));
  assert (capacity <= MAX_VECTORS);
  size_t available = capacity - old_stack_size;
  if (new_archive_vector_size > available) {
#if !defined(COMPACT)
    unsigned *old_begin_stack = BEGIN_STACK (*stack);
#endif
    unsigned enlarged = 0;
    do {
      assert (kissat_is_zero_or_power_of_two (capacity));

      if (capacity == MAX_VECTORS)
        kissat_fatal ("maximum archive_vector stack size "
                      "of 2^%u entries %s exhausted",
                      LD_MAX_VECTORS,
                      FORMAT_BYTES (MAX_VECTORS * sizeof (unsigned)));
      enlarged++;
      kissat_stack_enlarge (solver, (chars *) stack, sizeof (unsigned));

      capacity = CAPACITY_STACK (*stack);
      available = capacity - old_stack_size;
    } while (new_archive_vector_size > available);

    if (enlarged) {
#if !defined(COMPACT)
      unsigned *new_begin_stack = BEGIN_STACK (*stack);
      const ptrdiff_t moved =
          (char *) new_begin_stack - (char *) old_begin_stack;
#endif
#ifndef COMPACT
      if (moved)
        fix_archive_vector_pointers_after_moving_stack (solver, moved);
#endif
    }
    assert (capacity <= MAX_VECTORS);
    assert (new_archive_vector_size <= available);
  }
  unsigned *begin_old_archive_vector =
      begin_archive_vector (solver, archive_vector);
  unsigned *begin_new_archive_vector = END_STACK (*stack);
  unsigned *middle_new_archive_vector =
      begin_new_archive_vector + old_archive_vector_size;
  unsigned *end_new_archive_vector =
      begin_new_archive_vector + new_archive_vector_size;
  assert (end_new_archive_vector <= stack->allocated);
  const size_t old_bytes = old_archive_vector_size * sizeof (unsigned);
  const size_t delta_size =
      new_archive_vector_size - old_archive_vector_size;
  assert (MAX_SIZE_T / sizeof (unsigned) >= delta_size);
  const size_t delta_bytes = delta_size * sizeof (unsigned);
  if (old_bytes) {
    memcpy (begin_new_archive_vector, begin_old_archive_vector, old_bytes);
    memset (begin_old_archive_vector, 0xff, old_bytes);
  }
  solver->archive_vectors.usable += old_archive_vector_size;
  add_archive_usable (solver, delta_size);
  if (delta_bytes)
    memset (middle_new_archive_vector, 0xff, delta_bytes);
#ifdef COMPACT
  const uint64_t offset = SIZE_STACK (*stack);
  assert (offset <= MAX_VECTORS);
  archive_vector->offset = offset;
  LOG2 ("enlarged archive_vector at %p to %u[%u]", (void *) archive_vector,
        archive_vector->offset, archive_vector->size);
#else
  archive_vector->begin = begin_new_archive_vector;
  archive_vector->end = middle_new_archive_vector;
#ifdef LOGGING
  const size_t new_offset = archive_vector->begin - stack->begin;
  LOG2 ("enlarged archive_vector at %p to %zu[%zu]",
        (void *) archive_vector, new_offset, old_archive_vector_size);
#endif
#endif
  stack->end = end_new_archive_vector;
  assert (begin_new_archive_vector < end_new_archive_vector);
  assert (size_archive_vector (archive_vector) == old_archive_vector_size);
  return middle_new_archive_vector;
}

static inline void push_archive_vectors (kissat *solver,
                                         archive_vector *archive_vector,
                                         unsigned e) {
  unsigneds *stack = &solver->archive_vectors.stack;
  assert (e != INVALID_VECTOR_ELEMENT);
  if (
#ifdef COMPACT
      !archive_vector->size && !archive_vector->offset
#else
      !archive_vector->begin
#endif
  ) {
    if (EMPTY_STACK (*stack))
      PUSH_STACK (*stack, 0);
    if (FULL_STACK (*stack)) {
      unsigned *end = enlarge_archive_vector (solver, archive_vector);
      assert (*end == INVALID_VECTOR_ELEMENT);
      *end = e;
      dec_archive_usable (solver);
    } else {
#ifdef COMPACT
      assert ((uint64_t) SIZE_STACK (*stack) < MAX_VECTORS);
      archive_vector->offset = SIZE_STACK (*stack);
      assert (archive_vector->offset);
      *stack->end++ = e;
#else
      assert (stack->end < stack->allocated);
      *(archive_vector->begin = stack->end++) = e;
#endif
    }
#if !defined(COMPACT)
    archive_vector->end = archive_vector->begin;
#endif
  } else {
    unsigned *end = end_archive_vector (solver, archive_vector);
    if (end == END_STACK (*stack)) {
      if (FULL_STACK (*stack)) {
        end = enlarge_archive_vector (solver, archive_vector);
        assert (*end == INVALID_VECTOR_ELEMENT);
        *end = e;
        dec_archive_usable (solver);
      } else
        *stack->end++ = e;
    } else {
      if (*end != INVALID_VECTOR_ELEMENT)
        end = enlarge_archive_vector (solver, archive_vector);
      assert (*end == INVALID_VECTOR_ELEMENT);
      *end = e;
      dec_archive_usable (solver);
    }
  }
#ifndef COMPACT
  archive_vector->end++;
#else
  archive_vector->size++;
#endif
  check_archive_vectors (solver);
  check_archive_watches (solver);
}

static inline void push_blocking_archive_watch (kissat *solver,
                                                archive_watches *watches,
                                                int blocking,
                                                reference ref) {
  const archive_watch head = archive_blocking_archive_watch (blocking);
  PUSH_ARCHIVE_WATCHES (*watches, head);
  const archive_watch tail = archive_large_archive_watch (ref);
  PUSH_ARCHIVE_WATCHES (*watches, tail);
}

static inline void watch_archive_blocking (kissat *solver, int lit,
                                           int blocking, reference ref) {
  assert (ABS (lit) <= solver->max_var);
  assert (lit != 0);
  archive_watches *watches = &solver->archive_watches[lit2idx (lit)];
  push_blocking_archive_watch (solver, watches, blocking, ref);
}

static inline void watch_archive_reference (kissat *solver, int a, int b,
                                            reference ref) {
  assert (ABS (a) <= solver->max_var);
  assert (ABS (b) <= solver->max_var);
  watch_archive_blocking (solver, a, b, ref);
  watch_archive_blocking (solver, b, a, ref);
}

static inline void watch_archive_clause (kissat *solver,
                                         archive_clause *c) {
  assert (c->searched < c->size);
  const reference ref = reference_archive_clause (solver, c);
  watch_archive_reference (solver, c->lits[0], c->lits[1], ref);
}

void resize_archive_vector (kissat *solver, archive_vector *archive_vector,
                            size_t new_size) {
  const size_t old_size = size_archive_vector (archive_vector);
  assert (new_size <= old_size);
  if (new_size == old_size)
    return;
#ifdef COMPACT
  archive_vector->size = new_size;
#else
  archive_vector->end = archive_vector->begin + new_size;
#endif
  unsigned *begin = begin_archive_vector (solver, archive_vector);
  unsigned *end = begin + new_size;
  size_t delta = old_size - new_size;
  add_archive_usable (solver, delta);
  size_t bytes = delta * sizeof (unsigned);
  memset (end, 0xff, bytes);
  check_archive_vectors (solver);
#ifndef CHECK_VECTORS
  (void) solver;
#endif
}

void kissat_release_archive_vectors (kissat *solver) {
  RELEASE_STACK (solver->archive_vectors.stack);
  solver->archive_vectors.usable = 0;
}

void kissat_resize_archive_watches (kissat *solver, int max_var_old,
                                    int max_var_new) {
  if (!GET_OPTION (archive))
    return;
  const size_t block_size = sizeof (archive_watches);
  if (max_var_new > max_var_old) {
    archive_watches *new_watches =
        kissat_calloc (solver, 2 * max_var_new, block_size);
    if (max_var_old) {
      memcpy (new_watches, solver->archive_watches,
              2 * max_var_old * block_size);
      kissat_dealloc (solver, solver->archive_watches, 2 * max_var_old,
                      block_size);
    }
    solver->archive_watches = new_watches;
    solver->max_var = max_var_new;
  }
  if (max_var_new < max_var_old) {
    solver->archive_watches =
        kissat_nrealloc (solver, solver->archive_watches, max_var_old,
                         max_var_new, 2 * block_size);
    solver->max_var = max_var_new;
  }
}

void kissat_archive_init (kissat *solver) {
  solver->archive_unlocked = true;
}

void kissat_archive_clause (kissat *solver, clause *c) {
  if (!GET_OPTION (archive) || !solver->archive_unlocked)
    return;
  LOG ("Archive clause");
  const unsigned size = c->size;
  const reference res = allocate_archived_clause (solver, size);
  archive_clause *archive_c =
      unchecked_dereference_archive_clause (solver, res);

  for (uint i = 0; i < size; i++) {
    int lit = kissat_export_literal (solver, c->lits[i]);
    if (ABS (lit) > solver->max_var) {
      // In kissat_export_literal, there is a VALID_EXTERNAL_LITERAL
      // assertion, so we can safely assume this literal is not wrong
      kissat_resize_archive_watches (solver, solver->max_var, ABS (lit));
    }
    archive_c->lits[i] = lit;
  }
  archive_c->garbage = 0;
  archive_c->size = size;
  archive_c->searched = 2;

  check_archive_watches (solver);
  watch_archive_clause (solver, archive_c);
  check_archive_watches (solver);
}

void kissat_propagate_archive (kissat *solver) {
  if (!GET_OPTION (archive) || !solver->archive_unlocked)
    return;
  LOG ("Propagate archive begin");
  if (SIZE_STACK (solver->archive) == 0) {
    LOG ("Archive empty, exiting propagate_archive");
    return;
  }
  LOG ("Archive not empty, continue...");
  value *const values = solver->values;

  for (all_stack (unsigned, ilit, solver->archive_propagate)) {
    bool found_conflict = false;
    int lit = kissat_export_literal (solver, ilit);
    LOG ("Archive: propagate for ilit %d elit %d", ilit, lit);

    archive_watches *const all_watches = solver->archive_watches;
    archive_watches *watches = all_watches + lit2idx (-lit);
    if (size_archive_vector (watches) == 0) {
      LOG ("Archive: watches empty, exiting propagate_archive");
      return;
    }
    ward *const arena = BEGIN_STACK (solver->archive);

    archive_watch *const begin_watches = BEGIN_ARCHIVE_WATCHES (*watches);
    const archive_watch *const end_watches = END_ARCHIVE_WATCHES (*watches);

    archive_watch *q = begin_watches;
    const archive_watch *p = q;

    while (p != end_watches) {
      const archive_watch head = *q++ = *p++;
      assert (!head.blocking.binary);

      const int blocking = head.blocking.lit;
      if (!VALID_EXTERNAL_LITERAL (blocking)) {
        LOG ("Archive: blocking lit is not a valid external lit, remove "
             "from watch list");
        q -= 1;
        p++;
        continue;
      }
      uint iblocking = kissat_import_literal (solver, blocking);
      if (!VALID_INTERNAL_LITERAL (iblocking)) {
        LOG ("Archive: iblocking lit is not a valid internal lit, remove "
             "from watch list");
        q -= 1;
        p++;
        continue;
      }
      const value blocking_value = values[iblocking];
      archive_watch tail;

      tail = *q++ = *p++;
      assert (!tail.large.binary);

      if (blocking_value > 0)
        continue;
      const reference ref = tail.raw;
      assert (ref < SIZE_STACK (solver->archive));
      archive_clause *const c = (archive_clause *) (arena + ref);
      assert (c->size != 2);
      if (c->garbage) {
        LOG ("Archived clause is garbage, remove from watch list");
        q -= 2;
        continue;
      }
      int *const lits = BEGIN_LITS (c);
      int other = lits[0] ^ lits[1] ^ (-lit);
      assert (lits[0] != lits[1]);
      if (!VALID_EXTERNAL_LITERAL (other)) {
        LOG ("Archive: other lit is not a valid external lit, set to "
             "garbage and remove from watch list");
        c->garbage = true;
        q -= 2;
        continue;
      }
      assert (-lit != other);
      assert (lit != other);
      unsigned iother = kissat_import_literal (solver, other);
      if (!VALID_INTERNAL_LITERAL (iother)) {
        LOG ("Archive: iother lit is not a valid internal lit, set to "
             "garbage and remove from watch list");
        c->garbage = true;
        q -= 2;
        continue;
      }
      const value other_value = values[iother];
      if (other_value > 0) {
        q[-2].blocking.lit = other;
        continue;
      }
      const int *const end_lits = lits + c->size;
      int *const searched = lits + c->searched;
      assert (c->lits + 2 <= searched);
      assert (searched < end_lits);

      int *r;
      int replacement = INVALID_ELIT;
      value replacement_value = -1;
      for (r = searched; r != end_lits; r++) {
        replacement = *r;
        if (!VALID_EXTERNAL_LITERAL (replacement)) {
          LOG ("Archive: replacement is not a valid external lit, set to "
               "garbage and remove from watch list");
          c->garbage = true;
          q -= 2;
          goto NEXT_CLAUSE;
        }
        uint ireplacement = kissat_import_literal (solver, replacement);
        if (!VALID_INTERNAL_LITERAL (ireplacement)) {
          LOG ("Archive: ireplacement %d is not a valid internal lit, set "
               "to "
               "garbage and remove from watch list",
               ireplacement);
          c->garbage = true;
          q -= 2;
          goto NEXT_CLAUSE;
        }
        replacement_value = values[ireplacement];
        if (replacement_value >= 0)
          break;
      }
      if (replacement_value < 0) {
        for (r = lits + 2; r != searched; r++) {
          replacement = *r;
          if (!VALID_EXTERNAL_LITERAL (replacement)) {
            LOG ("Archive: replacement is not a valid external lit, set to "
                 "garbage and remove from watch list");
            c->garbage = true;
            q -= 2;
            goto NEXT_CLAUSE;
          }
          uint ireplacement = kissat_import_literal (solver, replacement);
          if (!VALID_INTERNAL_LITERAL (ireplacement)) {
            LOG ("Archive: ireplacement %d is not a valid internal lit, "
                 "set to "
                 "garbage and remove from watch list",
                 ireplacement);
            c->garbage = true;
            q -= 2;
            goto NEXT_CLAUSE;
          }
          replacement_value = values[ireplacement];
          if (replacement_value >= 0)
            break;
        }
      }
      if (replacement_value >= 0) {
        c->searched = r - lits;
        assert (c->searched < c->size);
        assert (replacement != INVALID_ELIT);
        q -= 2;
        lits[0] = other;
        lits[1] = replacement;
        assert (lits[0] != lits[1]);
        *r = -lit;
        LOG ("Archive: found replacement");
      } else if (other_value) {
        assert (replacement_value < 0);
        assert (blocking_value < 0);
        assert (other_value < 0);
        found_conflict = true;
        LOG ("Archive: conflict (increase archive_conflicts)");
        break;
      } else {
        assert (replacement_value < 0);
        LOG ("Archive: forcing (do nothing)");
      }
    NEXT_CLAUSE:;
    }
    while (p != end_watches)
      *q++ = *p++;
    SET_END_OF_ARCHIVE_WATCHES (*watches, q);
    if (found_conflict) {
      solver->statistics.archive_conflicts++;
      return;
    }
  }
}
