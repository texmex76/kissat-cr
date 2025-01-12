#ifndef _archive_h_INCLUDED
#define _archive_h_INCLUDED

#include "vector.h"
#include "clause.h"

typedef struct archive_clause archive_clause;

struct archive_clause {
  bool garbage : 1;
  uint searched;
  unsigned size;
  int lits[3]; // must be last!
};

typedef union archive_watch archive_watch;

typedef struct archive_vector archive_vector;
typedef struct archive_vectors archive_vectors;

struct archive_vectors {
  unsigneds stack;
  size_t usable;
};

struct archive_vector {
#ifdef COMPACT
  unsigned offset;
  unsigned size;
#else
  unsigned *begin;
  unsigned *end;
#endif
};

#define all_archive_clauses(C) \
  archive_clause *C = (archive_clause *) BEGIN_STACK (solver->archive), \
            *const C##_END = (archive_clause *) END_STACK (solver->archive), \
            *C##_NEXT; \
  C != C##_END && (C##_NEXT = next_archive_clause (C), true); \
  C = C##_NEXT

typedef struct binary_tagged_archive_literal archive_watch_type;
typedef struct binary_tagged_archive_literal binary_archive_watch;
typedef struct binary_tagged_archive_literal blocking_archive_watch;
typedef struct binary_tagged_archive_reference large_archive_watch;

struct binary_tagged_archive_literal {
#ifdef KISSAT_IS_BIG_ENDIAN
  bool binary : 1;
  int lit : 31;
#else
  int lit : 31;
  bool binary : 1;
#endif
};

struct binary_tagged_archive_reference {
#ifdef KISSAT_IS_BIG_ENDIAN
  bool binary : 1;
  unsigned ref : 31;
#else
  unsigned ref : 31;
  bool binary : 1;
#endif
};

union archive_watch {
  archive_watch_type type;
  binary_archive_watch binary;
  blocking_archive_watch blocking;
  large_archive_watch large;
  unsigned raw;
};

typedef archive_vector archive_watches;

#define BEGIN_ARCHIVE_WATCHES(WS) \
  ((union archive_watch *) begin_archive_vector (solver, &(WS)))

#define END_ARCHIVE_WATCHES(WS) \
  ((union archive_watch *) end_archive_vector (solver, &(WS)))

#define INVALID_ELIT INT_MAX

#define SET_END_OF_ARCHIVE_WATCHES(WS, P) \
  do { \
    size_t SIZE = (unsigned *) (P) -begin_archive_vector (solver, &WS); \
    resize_archive_vector (solver, &WS, SIZE); \
  } while (0)

#define PUSH_ARCHIVE_WATCHES(W, E) \
  do { \
    assert (sizeof (E) == sizeof (unsigned)); \
    push_archive_vectors (solver, &(W), (E).raw); \
  } while (0)

void check_archive_watches (struct kissat *solver);
void kissat_resize_archive_watches (struct kissat *solver, int max_var_old, int max_var_new);
void kissat_archive_clause (struct kissat *, clause *);
void kissat_propagate_archive(struct kissat *solver);
void kissat_release_archive_vectors (struct kissat *solver);
void kissat_archive_init (struct kissat *solver);

#endif
