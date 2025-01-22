#include "calc.h"

typedef struct indata {
  int alg;
  Node ideal;
} *Indata;

#define NEWINDATA(a) ((a)=(Indata)GC_malloc(sizeof(struct indata)))

typedef struct sugarp {
  LONG sugar;
  Poly p;
} *Sugarp;

#define NEWSUGARP(a) ((a)=(Sugarp)GC_malloc(sizeof(struct sugarp)))

typedef struct spair {
  LONG sugar;
  Monomial lcm;
  int i1,i2;
} *Spair;

#define NEWSPAIR(a) ((a)=(Spair)GC_malloc(sizeof(struct spair)))

typedef struct parray {
  int max,len,ishomo;
  Sugarp *body;
} *Parray;

Monomial div_monomial(Monomial m1,Monomial m2);
Monomial lcm_monomial(Monomial m1,Monomial m2);
Monomial dup_monomial(Monomial m1);
Monomial mul_monomial(Monomial m1,Monomial m2);

Node gb(Node);
Node f4(Node);
Spair create_spair(int i1,int i2);
int comp_spair(Spair a,Spair b);
Node insert_spair(Node l,Spair s);
Node poly_to_mnode(Poly p);
Sugarp spoly(Spair sp);
Sugarp rem_poly_sugar(Sugarp,Parray);
Poly monic_poly(Poly p);

LONG get_prime64(int ind);
int bitsize_z(Coef z);
int bitsize_mpz(mpz_ptr z);

LONG mulsubmod_64(LONG c,LONG a,LONG b,LONG m);

#define ALG_NOTIMP 0
#define ALG_BUCH 1
#define ALG_F4 2

typedef struct mononode {
	int max;
	Node *body;
} *Mononode;

#define NEWMONONODE(a) ((a)=(Mononode)GC_malloc(sizeof(struct mononode)))
