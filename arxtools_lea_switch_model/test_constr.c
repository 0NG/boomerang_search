/* 
 *  ARXtools - A toolkit for ARX analysis
 *
 *  Copyright: Gaëtan Leurent 2011-2012 <gaetan.leurent@normalesup.org>
 *
 *  To the extent possible under law, the author(s) have dedicated all
 *  copyright and related and neighboring rights to this software to the
 *  public domain worldwide. This software is distributed without any
 *  warranty.
 *
 *  You should have received a copy of the CC0 Public Domain Dedication
 *  along with this software. If not, see
 *  <http://creativecommons.org/publicdomain/zero/1.0/>.
 */


/* 
 * This tool is used to manipulate our new set of constraints
 * for differential analysis of ARX ciphers and hash functions.
 * 
 * You should first use build_fsm to construct the automata
 * for each operation used if the cipher.  Then use this tool
 * to compute the probabilities for each operation, and to to
 * propagate constraints.
 */

/*
 * WARNING:
 * Make sure that the automaton use the correct integer types!
 * The type used in this program is defined as state_t, modify it if needed.
 */


#define _XOPEN_SOURCE 700

#include <stdio.h>
#include <stdint.h>
#include <stdlib.h>
#include <sys/types.h>
#include <sys/stat.h>
#include <unistd.h>
#include <time.h>
#include <math.h>
#include <assert.h>
#include <setjmp.h>
#include <string.h>
#include <sys/stat.h>
#include <fcntl.h>
#ifndef _WIN32
#include <sys/mman.h>
#else
#include "mmap_windows.c"
#endif

#define tabsize(t) (sizeof(t)/sizeof((t)[0]))

int pow3(int n) {
  if (n==0)
    return 1;
  else
    return 3*pow3(n-1);
}

typedef int16_t state_t;

const state_t diff_count[][2][2][2][2][2][2] = {
  /*  0 */ {{{{{{ 0, -1}, {-1,  1}}, {{ 0, -1}, {-1, -1}}}, {{{ 0, -1}, {-1, -1}}, {{ 0, -1}, { 1, -1}}}}, {{{{ 0,  0}, { 1,  1}}, {{-1, -1}, {-1,  1}}}, {{{-1, -1}, {-1,  1}}, {{-1,  0}, {-1,  1}}}}}, {{{{{-1,  0}, { 1, -1}}, {{-1,  0}, {-1, -1}}}, {{{-1,  0}, {-1, -1}}, {{ 0,  0}, {-1, -1}}}}, {{{{-1, -1}, {-1, -1}}, {{-1, -1}, { 1, -1}}}, {{{-1, -1}, { 1, -1}}, {{-1, -1}, { 1,  1}}}}}}, 
  /*  1 */ {{{{{{ 0, -1}, {-1,  1}}, {{ 0, -1}, {-1, -1}}}, {{{-1, -1}, {-1,  1}}, {{ 0, -1}, { 1, -1}}}}, {{{{ 0,  0}, { 1,  1}}, {{-1, -1}, {-1,  1}}}, {{{ 0, -1}, {-1, -1}}, {{-1,  0}, {-1,  1}}}}}, {{{{{-1,  0}, { 1, -1}}, {{-1,  0}, {-1, -1}}}, {{{-1, -1}, { 1, -1}}, {{ 0,  0}, {-1, -1}}}}, {{{{-1, -1}, {-1, -1}}, {{-1, -1}, { 1, -1}}}, {{{-1,  0}, {-1, -1}}, {{-1, -1}, { 1,  1}}}}}}, 
};


#ifdef DEBUG
#define print_tab2(t,n) do {                            \
    printf ("Table %s:\n", #t);                         \
    for (unsigned int i__=0; i__<n; i__++)              \
      printf ("  %08x", t[i__]);                        \
    printf ("\n");                                      \
  } while(0)

#define print_var(v)                            \
  printf("Var %s: %08x\n", #v, v)

#define log_var(v,log) do {                     \
    printf("Var %s: %08x\n", #v, v);            \
    *(log++) = v;                               \
  } while(0)
#else
#define print_tab2(t,n)
#define print_var(v)
#define log_var(v,log)
#endif

#define print_tab(t) print_tab2(t, tabsize(t))


#define rotl32(x,n)   (((x) << (n)) | ((x) >> (32 - (n))))
#define rotr32(x,n)   (((x) >> (n)) | ((x) << (32 - (n))))

#define rotl64(x,n)   (((x) << (n)) | ((x) >> (64 - (n))))
#define rotr64(x,n)   (((x) >> (n)) | ((x) << (64 - (n))))


unsigned long long cnt = 0;
int best_s2 = -1;
unsigned int s2_stat[33] = {0};

int best_s1 = -1;
unsigned int s1_stat[33] = {0};

double cost;

#define MAX_PARAMS 12  // Increase if needed

typedef struct {
  struct reg *r;
  unsigned int rot;
} parameter;

typedef uint64_t word;
#define MAX_WORD_SIZE ((int)(8*sizeof(word)))
int WORD_SIZE = 32;

typedef struct {
  state_t *data;
  int nb_states;
  int nb_params;
  int nb_vars;
} automaton_t;

typedef struct {
  parameter p[MAX_PARAMS];
  automaton_t transition;
  automaton_t decision;
  automaton_t decision3;
} equation;

typedef struct reg {
  char bits[MAX_WORD_SIZE];
} reg;

typedef struct {
  unsigned int bad;
  unsigned int nb;
  state_t prev;
  char c;
} path_data;

// typedef used for counting solutions
// should allows relatively large numbers with good precision
// typedef long double bignum;
// Recent GCC also support __float128
typedef __float128 bignum;

typedef struct {
  bignum count;
} path_data_proba;


// Describe the set of constraints

#define CSTR_BITS 1
#define CSTR_MAX (1<<CSTR_BITS)

char constr_to_char[CSTR_MAX] = {'0', '1'};

void read_reg_from_str (reg *r, const char* s) {
  static char *to_const = NULL;
  if (!to_const) {
    to_const = malloc(256);
    memset (to_const, -1, 256);
    for (int i=0; i<CSTR_MAX; i++)
      if (constr_to_char[i])
        to_const[constr_to_char[i]] = i;
  }

  int i=0;
  for (; *s && i<WORD_SIZE; s++) {
    int c = to_const[*s];
    if (c == -1) {
      printf ("Warning: Unknown char: `%c'\n", *s);
    }
    r->bits[WORD_SIZE-1-i++] = c;
  }

  if (*s)
    printf ("Warning: string to long\n");

  if (i < WORD_SIZE) {
    printf ("Warning: string to short\n");
  }
}

void print_reg(reg *r) {
    printf("0b");
  for (int i=WORD_SIZE-1; i>=0; i--) {
    printf ("%c", constr_to_char[r->bits[i]]);
  }
}



/*
 * Returns the first failed bit.
 * Returns WORD_SIZE if system is actually compatible.
 *
 * Uses the decision automaton for better performance.
 */

int eq_compatible_upto(equation *eq) {

  parameter *in = eq->p;

  /* for (int i=0; i<npar; i++) { */
  /*   print_reg(in[i].r); printf (" "); */
  /* } */
  /* printf ("\n"); */

  state_t state = 0;

  if (eq->decision.data) {

    automaton_t *at = &eq->decision;
    int npar = at->nb_params;
    state_t (*aa)[1<<(CSTR_BITS*npar)] = (void*) at->data;
    
    int i;
    for (i=0; i < WORD_SIZE; i++) {
      unsigned int par = 0;
      for (int k=0; k<npar; k++) {
        par <<= CSTR_BITS;
        int x = in[k].r->bits[(i+in[k].rot) % WORD_SIZE];
        par  += x;
      }
      /* printf ("%4hx,%03x -> %4hx [%x]\n", state, par, aa[state][par], */
      /*         (char*)&aa[state][par] - (char*)aa); */
      state = aa[state][par];
      if ((unsigned) state == (unsigned) -1) {
        return i;
      }
    }
    
    return i;

  } else {
    fprintf (stderr, "Error: decision automaton not defined.\n");
    return -1;
  }
}

bignum eq_count(equation *eq) {

  automaton_t *at = &eq->transition;
  if (at->data == NULL) {
    fprintf (stderr, "Error: transition automaton not defined.\n");
    return -1;
  }

  int npar = at->nb_params;
  int nvar = at->nb_vars;
  int nst  = at->nb_states;
  parameter *in = eq->p;

  state_t (*aa)[1<<(CSTR_BITS*npar)][1<<nvar] = (void*) at->data;
  path_data_proba p[WORD_SIZE+1][nst];
  memset (p, 0, sizeof(p));
  p[0][0].count = 1;
  for (int i=0; i<WORD_SIZE; i++) {
    unsigned int par = 0;
    for (int k=0; k<npar; k++) {
      par <<= CSTR_BITS;
      int x = in[k].r->bits[(i+in[k].rot) % WORD_SIZE];
      par  += x;
    }
    for (int j=0; j<nst; j++) {
      if (p[i][j].count) {
	for (int zz = 0; zz < (1<<nvar); zz++) {
	  state_t z = aa[j][par][zz];
	  if (z != -1) {
	    path_data_proba *pp= &p[i+1][z];
            pp->count += p[i][j].count;
	  }
	}
      }
    }
  }

  bignum ret = 0;
  for (int i=0; i<nst; i++) {
    ret += p[WORD_SIZE][i].count;
  }
  printf("nst: %d\n", nst);

  return ret;
}

int eq_compatible(equation *eq) {
  if (eq->decision.data || eq->decision3.data)
    return eq_compatible_upto(eq) == WORD_SIZE;
  else
    return eq_count(eq)? 1: 0;    
}

int mmap_at (char *file, automaton_t *at) {
    int fd = open(file, O_RDONLY);

    if (fd < 0) {
      char buffer[32];
      snprintf (buffer, sizeof(buffer), "open %s", file);
      perror (buffer);
      return -1;
    }
    
    struct stat st;
    fstat(fd, &st);
    size_t size = st.st_size;
    at->data = mmap(NULL, size,
                PROT_READ, MAP_SHARED, fd, 0);
    if (at->data == MAP_FAILED) {
      perror ("mmap:");
      return -1;
    }
    at->nb_states = size;
    return 0;
}


int main (int argc, char* argv[]) {
    printf("bignum: %d bytes\n", sizeof(bignum));
  int propagate = 0;
  int cost = 0;

  int opt;

  int nvar = -1;
  int npar = -1;
  equation e;
  memset(&e, 0, sizeof(e));

  while ((opt = getopt(argc, argv, "w:vpcn:m:d:t:3:")) != -1) {

    switch (opt) {
    case 'v':
      propagate = 0;
      cost = 0;
      break;
    case 'p':
      propagate = 1;
      break;
    case 'c':
      cost = 1;
      break;

    case 'n':
      nvar = atoi(optarg);
      break;
    case 'm':
      npar = atoi(optarg);
      break;

    case 't':
      if (mmap_at(optarg, &e.transition))
        return -1;
      break;
    case 'd':
      if (mmap_at(optarg, &e.decision))
        return -1;
      break;
    case '3':
      if (mmap_at(optarg, &e.decision3))
        return -1;
      break;

    case 'w':
      WORD_SIZE = atoi(optarg);
      break;

    default:
    case '?':
    usage:
      printf ("Usage: %s [-w n] [-v|-p|-c] [-d file] [-t file] [-n n] [-m n]\n"
              "       -- cst1 [cst2 ...]\n"
              "\n"
              "    -w <n>: set word size\n"
              "\n"
              "    -v: only verify constraints (default) [requires -d]\n"
              "    -p: propagate constraints             [requires -d]\n"
              "    -c: count solutions                   [requires -t]\n"
              "\n"
              "    -d <file>: decision automaton\n"
              "    -3 <file>: tri-valued decision automaton\n"
              "    -t <file>: transition automaton       [requires -n]\n"
              "\n"
              "    -n <n>: number of variables\n"
              "    -m <n>: number of parameters\n", argv[0]);
    return -1;
    }
  }

  // Sanity checks 

  if (e.decision.data == NULL && e.transition.data == NULL && e.decision3.data == NULL && !cost) {
    fprintf(stderr, "Automaton needed (use -t/-d/-d3 option)\n");
    return -1;
  }
  if (e.decision.data != NULL && e.decision3.data != NULL) {
    fprintf(stderr, "Bad arguments (-d and -3 contradict)\n");
    return -1;
  }
  if (e.transition.data == NULL && cost) {
    fprintf(stderr, "Transition automaton needed (use -t option)\n");
    return -1;
  }

  if (cost && nvar == -1) {
    fprintf(stderr, "Number of variable needed (use -n option)\n");
    return -1;
  }

  if (argc == optind)
    goto usage;

  if (npar != -1) {
    if (npar != argc - optind)
      goto usage;
  } else {
    npar = argc - optind;
  }

  printf("npar: %d\n", npar);

  int dline = (( 1<<(npar*CSTR_BITS) ) * sizeof(state_t));
  assert((e.decision.nb_states % dline) == 0);
  e.decision.nb_states /= dline;
  e.decision.nb_params  = npar;
  e.decision.nb_vars    = nvar;

  int dline3 = (( pow3(npar) ) * sizeof(state_t));
  assert((e.decision3.nb_states % dline3) == 0);
  e.decision3.nb_states /= dline3;
  e.decision3.nb_params  = npar;
  e.decision3.nb_vars    = nvar;
  
  int tline = (( 1<<(npar*CSTR_BITS+nvar) ) * sizeof(state_t));
  assert((e.transition.nb_states % tline) == 0);
  e.transition.nb_states /= tline;
  e.transition.nb_params  = npar;
  e.transition.nb_vars    = nvar;

  reg regs[MAX_PARAMS];

  for (int i=0; i<argc-optind; i++) {
    e.p[i].r = &regs[i];
    e.p[i].rot = 0;
    read_reg_from_str(&regs[i], argv[optind+i]);
  }

  for (int i = 0; i < argc - optind; ++i) {
      print_reg(&regs[i]);
      printf(" ");
  }
  printf("\n");

  if (!eq_compatible(&e)) {
    if (e.decision.data || e.decision3.data)
      printf ("System fails at %2i\n", eq_compatible_upto(&e));
    else
      printf ("System fails\n");
  } else {
    printf ("System is compatible!\n");

    if (cost) {
      bignum p0 = eq_count(&e);
      printf ("#Sol: %llu (2^%f)\n", (unsigned long long)p0, log((double) p0)/log(2));
      char buf[128];
      int n = quadmath_snprintf (buf, sizeof buf, "%.10QF", p0);
      printf("%s\n", buf);
      return 0;

      if (npar > 1) {

        // Count the number of possible values for each parameter
        bignum counts[npar];
        bignum prod = 1;
        for (int i=0; i<npar; i++) {
          equation ee = {
            { e.p[i] },
            { (state_t*)diff_count, 2, 1, 2 },
            { NULL, 0, 0, 0 },
            { NULL, 0, 0, 0 }
          };
          counts[i] = eq_count(&ee);
          prod *= counts[i];
        }
        

        // Now compute probabilities with a random choice a a given parameter
        
        for (int i=0; i<npar; i++) {
          printf ("Cost[%i]: %.f\n", i,
                  -log((double)(p0*counts[i]/prod))/log(2));
        }
      }
    }

  }

  return 0;
}
