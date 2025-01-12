#include "internal.h"
#include "logging.h"
#include "math.h"
#include "print.h"
#include "tiers.h"

static double inverse_normal_cdf_lookup[] = {
    0.0,
    -2.3263478740408408,
    -2.0537489106318230,
    -1.8807936081512511,
    -1.7506860712521699,
    -1.6448536269514729,
    -1.5547735945968535,
    -1.4757910281791711,
    -1.4050715603096329,
    -1.3407550336902165,
    -1.2815515655446004,
    -1.2265281200366098,
    -1.1749867920660904,
    -1.1263911290388007,
    -1.0803193408149558,
    -1.0364333894937898,
    -0.9944578832097530,
    -0.9541652531461943,
    -0.9153650878428138,
    -0.8778962950512288,
    -0.8416212335729142,
    -0.8064212470182403,
    -0.7721932141886848,
    -0.7388468491852137,
    -0.7063025628400874,
    -0.6744897501960817,
    -0.6433454053929170,
    -0.6128129910166272,
    -0.5828415072712162,
    -0.5533847195556727,
    -0.5244005127080409,
    -0.4958503473474533,
    -0.4676987991145082,
    -0.4399131656732338,
    -0.4124631294414047,
    -0.3853204664075676,
    -0.3584587932511936,
    -0.3318533464368166,
    -0.3054807880993974,
    -0.2793190344474542,
    -0.2533471031357997,
    -0.2275449766411493,
    -0.2018934791418507,
    -0.1763741647808613,
    -0.1509692154967772,
    -0.1256613468550740,
    -0.1004337205114697,
    -0.0752698620998298,
    -0.0501535834647335,
    -0.0250689082587111,
    0.0000000000000000,
    0.0250689082587111,
    0.0501535834647337,
    0.0752698620998299,
    0.1004337205114699,
    0.1256613468550742,
    0.1509692154967774,
    0.1763741647808615,
    0.2018934791418511,
    0.2275449766411493,
    0.2533471031357997,
    0.2793190344474542,
    0.3054807880993974,
    0.3318533464368166,
    0.3584587932511938,
    0.3853204664075677,
    0.4124631294414050,
    0.4399131656732339,
    0.4676987991145084,
    0.4958503473474535,
    0.5244005127080410,
    0.5533847195556731,
    0.5828415072712162,
    0.6128129910166272,
    0.6433454053929170,
    0.6744897501960817,
    0.7063025628400874,
    0.7388468491852137,
    0.7721932141886848,
    0.8064212470182404,
    0.8416212335729143,
    0.8778962950512289,
    0.9153650878428143,
    0.9541652531461948,
    0.9944578832097535,
    1.0364333894937898,
    1.0803193408149558,
    1.1263911290388007,
    1.1749867920660904,
    1.2265281200366105,
    1.2815515655446004,
    1.3407550336902165,
    1.4050715603096329,
    1.4757910281791711,
    1.5547735945968539,
    1.6448536269514733,
    1.7506860712521708,
    1.8807936081512509,
    2.0537489106318225,
    2.3263478740408408,
};

static void compute_tier_limits (kissat *solver, bool stable,
                                 unsigned *tier1_ptr, unsigned *tier2_ptr) {
  statistics *statistics = &solver->statistics;
  int tiermode = GET_OPTION (tiermode);

  int tier1 = -1, tier2 = -1;
  switch (tiermode) {
  case 0:
    tier1 = GET_OPTION (tier1);
    tier2 = GET_OPTION (tier2);
    break;
  case 1: {
    uint64_t *used_stats = statistics->used[stable].glue;
    uint64_t total_used = 0;
    for (unsigned glue = 0; glue <= MAX_GLUE_USED; glue++)
      total_used += used_stats[glue];
    if (total_used) {
      uint64_t accumulated_tier1_limit = total_used * TIER1RELATIVE;
      uint64_t accumulated_tier2_limit = total_used * TIER2RELATIVE;
      uint64_t accumulated_used = 0;
      unsigned glue;
      for (glue = 0; glue <= MAX_GLUE_USED; glue++) {
        uint64_t glue_used = used_stats[glue];
        accumulated_used += glue_used;
        if (accumulated_used >= accumulated_tier1_limit) {
          tier1 = glue;
          break;
        }
      }
      if (accumulated_used < accumulated_tier2_limit) {
        for (glue = tier1 + 1; glue <= MAX_GLUE_USED; glue++) {
          uint64_t glue_used = used_stats[glue];
          accumulated_used += glue_used;
          if (accumulated_used >= accumulated_tier2_limit) {
            tier2 = glue;
            break;
          }
        }
      }
    }
  } break;
  case 2: {
    double mu = statistics->used[stable].mu;
    double sigma_sqr = statistics->used[stable].sigma_sqr;
    double used = stable ? (double) statistics->clauses_used_stable
                         : statistics->clauses_used_focused;
    double mu_ = mu / (1 - pow (1 - ALPHA, used));
    double sigma_sqr_ = sigma_sqr / (1 - pow (1 - ALPHA, used));
    // HACK: 0.00003 turned out to give reasonable tier2 values
    // for early iterations
    double mu__ = mu / (1 - pow (1 - 0.00003, used));
    double sigma_sqr__ = sigma_sqr / (1 - pow (1 - 0.00003, used));
    tier1 = (int) nearbyint (
        exp (mu_ +
             sqrt (sigma_sqr_) * inverse_normal_cdf_lookup[(int) nearbyint (
                                     TIER1RELATIVE * 100)]));
    tier2 = (int) nearbyint (
        exp (mu__ + sqrt (sigma_sqr__) *
                        inverse_normal_cdf_lookup[(int) nearbyint (
                            TIER2RELATIVE * 100)]));

  } break;
  default:
    abort ();
    break;
  }
  if (tier1 < 0) {
    tier1 = GET_OPTION (tier1);
    tier2 = MAX (GET_OPTION (tier2), tier1);
  } else if (tier2 < 0)
    tier2 = tier1;
  assert (0 <= tier1);
  assert (0 <= tier2);
  *tier1_ptr = tier1;
  *tier2_ptr = tier2;
  LOG ("%s tier1 limit %u", stable ? "stable" : "focused", tier1);
  LOG ("%s tier2 limit %u", stable ? "stable" : "focused", tier2);
}

void kissat_compute_and_set_tier_limits (struct kissat *solver) {
  bool stable = solver->stable;
  unsigned tier1, tier2;
  compute_tier_limits (solver, stable, &tier1, &tier2);
  solver->tier1[stable] = tier1;
  solver->tier2[stable] = tier2;
  kissat_phase (solver, "retiered", GET (retiered),
                "recomputed %s tier1 limit %u and tier2 limit %u "
                "after %" PRIu64 " conflicts",
                stable ? "stable" : "focused", tier1, tier2, CONFLICTS);
}

static unsigned decimal_digits (uint64_t i) {
  unsigned res = 1;
  uint64_t limit = 10;
  for (;;) {
    if (i < limit)
      return res;
    limit *= 10;
    res++;
  }
}

void kissat_print_tier_usage_statistics (kissat *solver, bool stable) {
  unsigned tier1, tier2;
  compute_tier_limits (solver, stable, &tier1, &tier2);
  statistics *statistics = &solver->statistics;
  uint64_t *used_stats = statistics->used[stable].glue;
  uint64_t total_used = 0;
  for (unsigned glue = 0; glue <= MAX_GLUE_USED; glue++)
    total_used += used_stats[glue];
  const char *mode = stable ? "stable" : "focused";
  //
  assert (used_stats[0] == 0);
  printf ("c %s glue array ", mode);
  for (unsigned glue = 1; glue < MAX_GLUE_USED + 1; glue++) {
    printf ("%lu ", used_stats[glue]);
  }
  fputs ("\n", stdout);
  printf ("c %s glue array dist ", mode);
  for (unsigned glue = 1; glue < MAX_GLUE_USED + 1; glue++) {
    printf ("%f ", (double) used_stats[glue] / total_used);
  }
  fputs ("\n", stdout);
  //
  assert (tier1 <= tier2);
  unsigned span = tier2 - tier1 + 1;
  const unsigned max_printed = 5;
  assert (max_printed & 1), assert (max_printed / 2 > 0);
  unsigned prefix, suffix;
  if (span > max_printed) {
    prefix = tier1 + max_printed / 2 - 1;
    suffix = tier2 - max_printed / 2 + 1;
  } else
    prefix = UINT_MAX, suffix = 0;
  uint64_t accumulated_middle = 0;
  int glue_digits = 1, clauses_digits = 1;
  for (unsigned glue = 0; glue <= MAX_GLUE_USED; glue++) {
    if (glue < tier1)
      continue;
    uint64_t used = used_stats[glue];
    int tmp_glue = 0, tmp_clauses = 0;
    if (glue <= prefix || suffix <= glue) {
      tmp_glue = decimal_digits (glue);
      tmp_clauses = decimal_digits (used);
    } else {
      accumulated_middle += used;
      if (glue + 1 == suffix) {
        tmp_glue = decimal_digits (prefix + 1) + decimal_digits (glue) + 1;
        tmp_clauses = decimal_digits (accumulated_middle);
      }
    }
    if (tmp_glue > glue_digits)
      glue_digits = tmp_glue;
    if (tmp_clauses > clauses_digits)
      clauses_digits = tmp_clauses;
    if (glue == tier2)
      break;
  }
  char fmt[32];
  sprintf (fmt, "%%%d" PRIu64, clauses_digits);
  accumulated_middle = 0;
  uint64_t accumulated = 0;
  for (unsigned glue = 0; glue <= MAX_GLUE_USED; glue++) {
    uint64_t used = used_stats[glue];
    accumulated += used;
    if (glue < tier1)
      continue;
    if (glue <= prefix || suffix <= glue + 1) {
      fputs ("c ", stdout);
      fputs (mode, stdout);
      fputs (" glue ", stdout);
    }
    if (glue <= prefix || suffix <= glue) {
      int len = printf ("%u", glue);
      while (len > 0 && len < glue_digits)
        fputc (' ', stdout), len++;
      fputs (" used ", stdout);
      printf (fmt, used);
      printf (" clauses %5.2f%% accumulated %5.2f%%",
              kissat_percent (used, total_used),
              kissat_percent (accumulated, total_used));
      if (glue == tier1)
        fputs (" tier1", stdout);
      if (glue == tier2)
        fputs (" tier2", stdout);
      fputc ('\n', stdout);
    } else {
      accumulated_middle += used;
      if (glue + 1 == suffix) {
        int len = printf ("%u-%u", prefix + 1, suffix - 1);
        while (len > 0 && len < glue_digits)
          fputc (' ', stdout), len++;
        fputs (" used ", stdout);
        printf (fmt, accumulated_middle);
        printf (" clauses %5.2f%% accumulated %5.2f%%\n",
                kissat_percent (accumulated_middle, total_used),
                kissat_percent (accumulated, total_used));
      }
    }
    if (glue == tier2)
      break;
  }
}
