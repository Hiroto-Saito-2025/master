#include "gb.h"

Coef one_z()
{
  Coef r;

  NEWZ(r.z);
  mpz_init(r.z);
  mpz_set_si(r.z,1);
  return r;
}

void print_mpz(mpz_ptr a)
{
  mpz_out_str(stdout,10,a);
  printf("\n");
}

void print_z(Coef a)
{
  if ( a.z == 0 )
    printf("0");
  else
    mpz_out_str(stdout,10,a.z);
}

int bitsize_mpz(mpz_ptr t)
{
  return mpz_sizeinbase(t,2);
}

int bitsize_z(Coef t)
{
  if ( t.f == 0 ) return 0;
  else return mpz_sizeinbase(t.z,2);
}

int zero_z(Coef t)
{
  return t.z == 0;
}

Coef mpztoc(mpz_ptr t)
{
  Coef z;

  if ( mpz_sgn(t) == 0 ) {
    z.z = 0;
    return z;
  } else {
    NEWZ(z.z);
    z.z[0] = t[0];
    return z;
  }
}

Coef add_z(Coef a,Coef b)
{
  mpz_t t;

  if ( !a.z ) return b;
  else if ( !b.z ) return a;
  else {
    mpz_init(t); mpz_add(t,a.z,b.z);
    return mpztoc(t);
  }
}

Coef neg_z(Coef a)
{
  mpz_t t;

  if ( a.z == 0 ) return a;
  else {
    mpz_init(t); mpz_neg(t,a.z);
    return mpztoc(t);
  }
}

Coef sub_z(Coef a,Coef b)
{
  mpz_t t;

  if ( !a.z ) return neg_z(b);
  else if ( !b.z ) return a;
  else {
    mpz_init(t); mpz_sub(t,a.z,b.z);
    return mpztoc(t);
  }
}

Coef mul_z(Coef a,Coef b)
{
  mpz_t t;

  if ( a.z == 0 ) return a;
  else if ( b.z == 0 ) return b;
  else {
    mpz_init(t); mpz_mul(t,a.z,b.z);
    return mpztoc(t);
  }
}

Coef divexact_z(Coef a,Coef b)
{
  mpz_t t;

  if ( b.z == 0 ) {
    error("div_z : division by 0");
    return b; // dummy return
  } else if ( a.z == 0 ) return a;
  else {
    mpz_init(t); mpz_divexact(t,a.z,b.z);
    return mpztoc(t);
  }
}

Coef gcd_z(Coef a,Coef b)
{
  mpz_t t;

  if ( a.z == 0 ) return b;
  else if ( b.z == 0 ) return a;
  else {
    mpz_init(t); mpz_gcd(t,a.z,b.z);
    return mpztoc(t);
  }
}


Coef ntoc_z(char *n)
{
  mpz_t t;

  mpz_init(t);
  mpz_set_str(t,n,10);
  return mpztoc(t);
}
