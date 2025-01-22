#include "gb.h"
#include <time.h>

Ring CurrentRing;
FILE *Input;
struct parray gbarray;
struct sigparray siggbarray;
struct sarray syzarray;
extern Indata result;
int criB,criF,criM,criD;
int opt_modorder;

void *GC_calloc_atomic(size_t n)
{
  void *p;
  p = GC_malloc_atomic(n);
  memset(p,0,n);
  return p;
}

void error(char *msg)
{
  fprintf(stderr,"%s\n",msg);
  exit(0);
}

Node append_to_node(Node p,void *obj)
{
  Node q,r;

  NEWNODE(r); r->body = obj; r->next = 0;
  if ( p == 0 ) {
    return r;
  } else {
    for ( q = p; q->next != 0; q = q->next);
    q->next = r;
    return p;
  }
}

// exp should be placed in the reverse order.
// (e1 ... en) -> (en ... e1)

int mcomp_simple(Monomial a,Monomial b)
{
  int i,w,ret;

  if ( CurrentRing->graded ) {
    if ( a->td > b->td ) return 1;
    else if ( a->td < b->td ) return -1;
  }
  w = CurrentRing->wpe;
  ret = CurrentRing->rev?-1:1;
  for ( i = 0; i < w; i++ )
    if ( a->exp[i] > b->exp[i] ) return ret;
    else if ( a->exp[i] < b->exp[i] ) return -ret;
  return 0;
}

int length(Node p)
{
  int i;
  for ( i = 0; p; p = p->next, i++ );
  return i;
}

int ishomo_poly(Poly p)
{
  LONG td;
  Poly q;

  if ( p == 0 ) return 1;
  td = p->m->td;
  for ( q = p->next; q != 0; q = q->next )
    if ( q->m->td != td ) return 0;
  return 1;
}

LONG tdeg_poly(Poly p)
{
  LONG td;
  Poly q;

  if ( p == 0 ) return -1;
  td = 0;
  for ( q = p; q != 0; q = q->next )
    if ( q->m->td > td ) td = q->m->td;
  return td;
}

Poly neg_poly(Poly p)
{
  struct poly root;
  Poly q,r,s;

  if ( p == 0 ) return p;
  r = &root;
  for ( q = p; q != 0; q = q->next ) {
     APPENDPOLY(r,s,CurrentRing->negc(q->c),q->m);
  }
  r->next = 0;
  return root.next;
}

Poly add_poly(Poly p1,Poly p2)
{
  struct poly root;
  Poly r,q1,q2,q;
  Coef c;
  int (*mcomp)(Monomial,Monomial);

  if ( p1 == 0 )
    return p2;
  else if ( p2 == 0 )
    return p1;
  else {
    r = &root;
    mcomp = CurrentRing->mcomp;
    for ( q1 = p1, q2 = p2; q1 != 0 && q2 != 0; ) {
      switch ( (*mcomp)(q1->m,q2->m) ) { 
        case 0:
          c = CurrentRing->addc(q1->c,q2->c);
          if ( !CurrentRing->zeroc(c) ) {
            APPENDPOLY(r,q,c,q1->m);
          }
          q1 = q1->next; q2 = q2->next;
          break;
        case 1:
          APPENDPOLY(r,q,q1->c,q1->m);
          q1 = q1->next;
          break;
        case -1:
          APPENDPOLY(r,q,q2->c,q2->m);
          q2 = q2->next;
          break;
      }
    }
    if ( q1 ) {
      r->next = q1;
    } else {
      r->next = q2;
    }
    return root.next;
  }
}

Poly merge_poly(Poly p1,Poly p2)
{
  struct poly root;
  Poly r,q1,q2,q,t;
  Coef c;
  int (*mcomp)(Monomial,Monomial);

  if ( p1 == 0 )
    return p2;
  else if ( p2 == 0 )
    return p1;
  else {
    r = &root;
    mcomp = CurrentRing->mcomp;
    for ( q1 = p1, q2 = p2; q1 != 0 && q2 != 0; ) {
      switch ( (*mcomp)(q1->m,q2->m) ) { 
        case 0:
          c = CurrentRing->addc(q1->c,q2->c);
          if ( !CurrentRing->zeroc(c) ) {
            q1->c = c; r->next = q1; r = q1; q1 = q1->next; 
          } else {
            t = q1->next; /*GC_free(q1->m); GC_free(q1);*/ q1 = t;
          }
          t = q2->next; /*GC_free(q2->m); GC_free(q2);*/ q2 = t;
          break;
        case 1:
          r->next = q1; r = q1;
          q1 = q1->next;
          break;
        case -1:
          r->next = q2; r = q2;
          q2 = q2->next;
          break;
      }
    }
    if ( q1 )
      r->next = q1;
    else
      r->next = q2;
    return root.next;
  }
}

// p1 and p2 are lists of Monomials
Node merge_mnode(Node p1,Node p2)
{
  struct node root;
  Node q1,q2,r,cur,t;
  int (*mcomp)(Monomial,Monomial);

  r = &root;
  cur = p1; q2 = p2;
  mcomp = CurrentRing->mcomp;
  for ( q1 = p1, q2 = p2; q1 != 0 && q2 != 0; ) {
    switch ( (*mcomp)((Monomial)q1->body,(Monomial)q2->body) ) { 
      case 0:
        r->next = q1; r = q1; q1 = q1->next; 
        t = q2->next; GC_free(q2); q2 = t;
        break;
      case 1:
        r->next = q1; r = q1;
        q1 = q1->next;
        break;
      case -1:
        r->next = q2; r = q2;
        q2 = q2->next;
        break;
    }
  }
  if ( q1 )
    r->next = q1;
  else
    r->next = q2;
  return root.next;
}

Node symb_merge_poly(Node p1,Poly p2)
{
  struct node root;
  Node q1,r,s;
  Poly t,q2;
  int (*mcomp)(Monomial,Monomial);

  r = &root;
  mcomp = CurrentRing->mcomp;
  for ( q1 = p1, q2 = p2; q1 != 0 && q2 != 0; ) {
    switch ( (*mcomp)((Monomial)q1->body,q2->m) ) { 
      case 0:
        r->next = q1; r = q1; q1 = q1->next; 
        t = q2->next; q2 = t;
        break;
      case 1:
        r->next = q1; r = q1;
        q1 = q1->next;
        break;
      case -1:
        APPENDNODE(r,s,q2->m);
        q2 = q2->next;
        break;
    }
  }
  if ( q1 ) {
    r->next = q1;
  } else {
    r->next = poly_to_mnode(q2);
  }
  return root.next;
}

Poly sub_poly(Poly p1,Poly p2)
{
  return add_poly(p1,neg_poly(p2));
}

Poly mulc_poly(Coef c,Poly p)
{
  struct poly root;
  Poly q,r,s;

  r = &root;
  for ( q = p; q != 0; q = q->next ) {
     APPENDPOLY(r,s,CurrentRing->mulc(c,q->c),q->m);
  }
  r->next = 0;
  return root.next;
}

Coef cont_poly_z(Poly p)
{
  Coef gcd,c;
  Poly t;

  if ( p == 0 ) {
    gcd.z = 0; return gcd;
  }
  gcd = p->c;
  for ( t = p->next; t != 0; t = t->next )
    gcd = gcd_z(gcd,t->c);
  return gcd;
}

// exact division 
Poly div_poly_z(Coef c,Poly p)
{
  struct poly root;
  Poly q,r,s;
  Coef c1;

  r = &root;
  for ( q = p; q != 0; q = q->next ) {
     c1 = divexact_z(q->c,c);
     APPENDPOLY(r,s,c1,q->m);
     r->next = s; r = s;
  }
  r->next = 0;
  return root.next;
}

Poly removecont_poly_z(Poly p)
{
  Coef gcd;

  gcd = cont_poly_z(p);
  return div_poly_z(gcd,p);
}

void cont_vector_mpz(mpz_t cont,mpz_t *p,int len)
{
  int i,j;
  mpz_t sum;
  static mpz_t *w;
  static int w_len=0;

  mpz_init(cont);
  if ( w_len < len ) {
    w = (mpz_t *)GC_malloc(len*sizeof(mpz_t));
    w_len = len;
  }
  memcpy(w,p,len*sizeof(mpz_t));
  qsort(w,len,sizeof(mpz_t),(int (*)(const void *,const void *))mpz_cmpabs);
  for ( i = 0; i < len && mpz_sgn(w[i]) == 0; i++ );
  if ( i == len ) {
    mpz_set_ui(cont,1);
  } else {
    mpz_set(cont,w[i]);
    if ( mpz_cmp_si(cont,1) == 0 ) return;
    if ( mpz_cmp_si(cont,-1) == 0 ) {
      mpz_set_ui(cont,1);
      return;
    }
    mpz_init_set_ui(sum,0);
    for ( j = i+1; j < len; j++ ) mpz_add(sum,sum,w[j]);
    mpz_gcd(cont,cont,sum);
    for ( j = i+1; j < len; j++ ) mpz_gcd(cont,cont,w[j]);
  }
}

// exact division 
void div_vector_mpz(mpz_t c,mpz_t *p,int len)
{
  int i;

  for ( i = 0; i < len; i++ ) mpz_divexact(p[i],p[i],c);
}

void removecont_vector_mpz(mpz_t *p,int len)
{
  mpz_t cont;

  cont_vector_mpz(cont,p,len);
  div_vector_mpz(cont,p,len);
}


int bitsize_vector_mpz(mpz_t *p,int len)
{
  int size,i;

  for ( size = 0, i = 0; i < len; i++ )
    size += bitsize_mpz(p[i]);
  return size;
}

Monomial dup_monomial(Monomial m1)
{
  Monomial m;
  int w,i;

  NEWMONOMIAL(m);
  w = CurrentRing->wpe;
  m->td = m1->td;
  for ( i = 0; i < w; i++ ) m->exp[i] = m1->exp[i];
  return m;
}

Monomial mul_monomial(Monomial m1,Monomial m2)
{
  Monomial m;
  int w,i;

  NEWMONOMIAL(m);
  w = CurrentRing->wpe;
  m->td = m1->td+m2->td;
  for ( i = 0; i < w; i++ ) m->exp[i] = m1->exp[i]+m2->exp[i];
  return m;
}

Monomial div_monomial(Monomial m1,Monomial m2)
{
  Monomial m;
  int w,i;

  NEWMONOMIAL(m);
  w = CurrentRing->wpe;
  m->td = m1->td-m2->td;
  for ( i = 0; i < w; i++ ) m->exp[i] = m1->exp[i]-m2->exp[i];
  return m;
}

int relprime_monomial(Monomial lcm,Monomial m1,Monomial m2)
{
  int w,i;

  w = CurrentRing->wpe;
  if ( lcm->td != m1->td + m2->td )
    return 0;
  for ( i = 0; i < w; i++ ) 
    if ( lcm->exp[i] != m1->exp[i]+m2->exp[i] )
      return 0;
  return 1;
}

#if 1
Monomial lcm_monomial(Monomial m1,Monomial m2)
{
  ULONG mask,e,e1,e2;
  LONG td;
  int nv,bpe,i,shift,bpos,wpos;
  Monomial m;

  nv = CurrentRing->nv;
  bpe = CurrentRing->bpe;
  if ( bpe == 8 ) mask = ~0;
  else mask = (((ULONG)1)<<(bpe*8))-1;
  NEWMONOMIAL(m);
  td = 0;
  for ( i = 0; i < nv; i++ ) {
    bpos = i*bpe; wpos = bpos/8; shift = (8-bpe-(bpos%8))*8;
    e1 = (m1->exp[wpos] >> shift)&mask;
    e2 = (m2->exp[wpos] >> shift)&mask;
    if ( e1>e2 ) e = e1;
    else e = e2;
    td += e;
    m->exp[wpos] |= (e<<shift);
  }
  m->td = td;
  return m;
}
#else
ULONG lcm_LONG(ULONG w1,ULONG w2,LONG *tdp)
{
  ULONG r,w,d1,d2;
  LONG td;
  r = 0;
  td = 0;
  switch ( CurrentRing->bpe ) {
    case 1:
      d1=w1&0xff; d2=w2&0xff; w = d1>d2?d1:d2; r |= w; td += w;
      d1=w1&0xff00; d2=w2&0xff00; w = d1>d2?d1:d2; r |= w; td += w>>8;
      d1=w1&0xff0000; d2=w2&0xff0000; w = d1>d2?d1:d2; r |= w; td += w>>16;
      d1=w1&0xff000000; d2=w2&0xff000000; w = d1>d2?d1:d2; r |= w; td += w>>24;
      d1=w1&0xff00000000; d2=w2&0xff00000000; w = d1>d2?d1:d2; r |= w; td += w>>32;
      d1=w1&0xff0000000000; d2=w2&0xff0000000000; w = d1>d2?d1:d2; r |= w; td += w>>40;
      d1=w1&0xff000000000000; d2=w2&0xff000000000000; w = d1>d2?d1:d2; r |= w; td += w>>48;
      d1=w1&0xff00000000000000; d2=w2&0xff00000000000000; w = d1>d2?d1:d2; r |= w; td += w>>56;
      break;
    case 2:
      d1=w1&0xffff; d2=w2&0xffff; w = d1>d2?d1:d2; r |= w; td += w;
      d1=w1&0xffff0000; d2=w2&0xffff0000; w = d1>d2?d1:d2; r |= w; td += w>>16;
      d1=w1&0xffff00000000; d2=w2&0xffff00000000; w = d1>d2?d1:d2; r |= w; td += w>>32;
      d1=w1&0xffff000000000000; d2=w2&0xffff000000000000; w = d1>d2?d1:d2; r |= w; td += w>>48;
      break;
    case 4:
      d1=w1&0xffffffff; d2=w2&0xffffffff; w = d1>d2?d1:d2; r |= w; td += w;
      d1=w1&0xffffffff00000000; d2=w2&0xffffffff00000000; w = d1>d2?d1:d2; r |= w; td += w>>32;
      break;
    case 8:
      r = w1>w2?w1:w2; td = r;
      break;
  }
  *tdp = td;
  return r;
}

Monomial lcm_monomial(Monomial m1,Monomial m2)
{
  int w,i;
  Monomial m;
  LONG td,d;

  NEWMONOMIAL(m);
  w = CurrentRing->wpe;
  td = 0;
  for ( i = 0; i < w; i++ ) {
    m->exp[i] = lcm_LONG(m1->exp[i],m2->exp[i],&d);
    td += d;
  }
  m->td = td;
  return m;
}
#endif

int eq_monomial(Monomial m1,Monomial m2)
{
  int w,i;

  if ( m1->td != m2->td ) return 0;
  w = CurrentRing->wpe;
  for ( i = 0; i < w; i++ ) if ( m1->exp[i] != m2->exp[i] ) return 0;
  return 1;
}

#if 0
int divisible(Monomial dnd,Monomial dvr)
{
  ULONG mask,ednd,edvr;
  int nv,bpe,i,shift,bpos,wpos;

  if ( dnd->td < dvr->td ) return 0;

  nv = CurrentRing->nv;
  bpe = CurrentRing->bpe;
  if ( bpe == 8 ) mask = ~0;
  else mask = (((ULONG)1)<<(bpe*8))-1;
  for ( i = 0; i < nv; i++ ) {
    bpos = i*bpe; wpos = bpos/8; shift = 8-bpe-(bpos%8);
    ednd = (dnd->exp[wpos] >> (shift*8))&mask;
    edvr = (dvr->exp[wpos] >> (shift*8))&mask;
    if ( ednd < edvr ) return 0;
  }
  return 1;
}
#else
int divisible(Monomial dnd,Monomial dvr)
{
  int w,i;
  ULONG sb;

  sb = CurrentRing->sb;
  if ( dnd->td < dvr->td ) return 0;
  w = CurrentRing->wpe;
  for ( i = 0; i < w; i++ ) if ( (dnd->exp[i]-dvr->exp[i])&sb ) return 0;
  return 1;
}
#endif

Poly mul1_poly(Poly p1,Poly p2)
{
  struct poly root;
  Poly p,q,r,s;
  Coef c,c1;
  Monomial m;

  r = &root;
  c = p1->c;
  for ( q = p2; q != 0; q = q->next ) {
     c1 = CurrentRing->mulc(c,q->c); 
     m = mul_monomial(p1->m,q->m);
     APPENDPOLY(r,s,c1,m);
  }
  r->next = 0;
  return root.next;
}

Poly mul_poly(Poly p1,Poly p2)
{
  Poly r,p,q;

  r = 0;
  for ( q = p1; q != 0; q = q->next ) {
    p = mul1_poly(q,p2);
    r = merge_poly(r,p);
  }
  return r;
}

// p2 should be a constant
Poly divc_poly(Poly p1,Poly p2)
{
  struct poly root;
  Poly q,r,s;
  Coef c,c1;

  if ( p2 == 0 )
    error("divc_poly : division by 0");
  if ( p2->m->td != 0 )
    error("divc_poly : division by a non constant poly");
  if ( CurrentRing->divc == 0 )
    error("divc_poly : division is not allowed");
  r = &root;
  c = p2->c;
  for ( q = p1; q != 0; q = q->next ) {
     c1 = CurrentRing->divc(q->c,c); 
     APPENDPOLY(r,s,c1,p1->m);
  }
  r->next = 0;
  return root.next;
}

Poly power_poly(Poly p,char *q)
{
  Poly r,pi;
  int e;
 
  e = strtol(q,0,10);
  if ( e < 0 )
    error("power_poly : exponent must be non-negative");
  // e = sum ei*2^i => p^e = prod_{ei=1} p^(2^i)
  // pi <- p^(2^0)=p; r <- 1
  NEWPOLY(r);
  NEWMONOMIAL(r->m);
  r->c = CurrentRing->one;
  pi = p;
  while ( e != 0 ) {
    if ( (e&1) != 0 )
      r = mul_poly(r,pi);
    pi = mul_poly(pi,pi);
    e >>= 1;
  }
  return r;
}

Poly reducer(Monomial m1,Poly p2)
{
  Monomial m;
  Poly p;

  m = div_monomial(m1,p2->m);
  NEWPOLY(p); p->c = CurrentRing->one; p->m = m; p->next = 0;
  return mul1_poly(p,p2);
}

// functions for sugarp

Sugarp red_poly_sugar(Sugarp p1,Sugarp p2)
{
  Monomial m;
  Coef c,z;
  Poly p;
  Sugarp s;
  LONG s1,s2;

  m = div_monomial(p1->p->m,p2->p->m);
  c = CurrentRing->divc(p1->p->c,p2->p->c);
//  z.f = 0;
//  c = CurrentRing->subc(z,c);
  c = CurrentRing->negc(c);
  NEWPOLY(p); p->c = c; p->m = m; p->next = 0;
  NEWSUGARP(s);
  s->p = merge_poly(p1->p,mul1_poly(p,p2->p));
  s1 = p1->sugar;
  s2 = p2->sugar + m->td;
  if ( s1 > s2 ) s->sugar = s1;
  else s->sugar = s2;
  return s;
}

Sugarp red_poly_sugar_z(Sugarp p1,Sugarp p2,Coef *mul)
{
  Monomial m;
  Coef c,z;
  Poly p,q1,q2;
  Sugarp s;
  LONG s1,s2;
  mpz_t gcd,c1,c2;

  m = div_monomial(p1->p->m,p2->p->m);
  mpz_init(gcd); mpz_gcd(gcd,p1->p->c.z,p2->p->c.z);
  mpz_init(c1); mpz_div(c1,p2->p->c.z,gcd);
  mpz_init(c2); mpz_div(c2,p1->p->c.z,gcd); mpz_neg(c2,c2);
  *mul = mpztoc(c1);
  q1 = mulc_poly(*mul,p1->p);
  NEWPOLY(p); p->c = mpztoc(c2); p->m = m; p->next = 0;
  q2 = mul1_poly(p,p2->p);
  NEWSUGARP(s);
  s->p = merge_poly(q1,q2);
  s1 = p1->sugar;
  s2 = p2->sugar + m->td;
  if ( s1 > s2 ) s->sugar = s1;
  else s->sugar = s2;
  return s;
}

Sugarp spoly(Spair sp)
{
  Monomial lcm,m1;
  Poly q1;
  Sugarp p1,p2,s1;
  int i1,i2;
  Coef mul;

  i1 = sp->i1;
  i2 = sp->i2;
  p1 = gbarray.body[i1];
  p2 = gbarray.body[i2];
  lcm = sp->lcm;
  m1 = div_monomial(lcm,p1->p->m);
  NEWPOLY(q1); q1->c = p2->p->c; q1->m = m1; q1->next = 0;
  NEWSUGARP(s1);
  s1->sugar = p1->sugar + m1->td;
  s1->p = mul1_poly(q1,p1->p);
  if ( CurrentRing->chr != 0 )
    return red_poly_sugar(s1,p2);
  else
    return red_poly_sugar_z(s1,p2,&mul);
}

Sugarp rem_poly_sugar(Sugarp p,Parray a)
{
  struct poly root;
  Poly r,x;
  Sugarp s;
  Sugarp *pa;
  int i,len;

//  print_poly(p->p); printf("\n");
  r = &root;
  NEWSUGARP(s); *s = *p;
  pa = a->body;
  len = a->len;
  while ( s->p != 0 ) {
    for ( i = 0; i < len; i++ ) {
      if ( divisible(s->p->m,pa[i]->p->m) ) break;
    }
    if ( i < len ) {
      s = red_poly_sugar(s,pa[i]);
//      printf("->"); print_poly(s->p); printf("\n");
    } else {
      NEWPOLY(x); *x = *(s->p); r->next = x; r = x;
      s->p = s->p->next;
    }
  }
  r->next = 0;
  s->p = root.next;
  return s;
}

Sugarp rem_poly_sugar_z(Sugarp p,Parray a)
{
  struct poly root;
  Poly r,x,t;
  Sugarp s;
  Sugarp *pa;
  int i,len;
  Coef mul;

//  print_poly(p->p); printf("\n");
  r = &root; r->next = 0;
  NEWSUGARP(s); *s = *p;
  pa = a->body;
  len = a->len;
  while ( s->p != 0 ) {
    for ( i = 0; i < len; i++ ) {
      if ( divisible(s->p->m,pa[i]->p->m) ) break;
    }
    if ( i < len ) {
      s = red_poly_sugar_z(s,pa[i],&mul);
//      printf("->"); print_poly(s->p); printf("\n");
      for ( t = root.next; t != 0; t = t->next )
        t->c = CurrentRing->mulc(t->c,mul);
    } else {
      NEWPOLY(x); *x = *(s->p); r->next = x; r = x; r->next = 0;
      s->p = s->p->next;
    }
  }
  r->next = 0;
  s->p = root.next;
  return s;
}

Node poly_to_mnode(Poly p)
{
  struct node root;
  Node r,t;
  Poly q;

  r = &root;
  for ( q = p; q != 0; q = q->next ) {
    APPENDNODE(r,t,q->m);
  }
  r->next = 0;
  return root.next;
}

LONG find_pos(Monomial m,Monomial *marray,int len)
{
  int max,min,mid,c;
  int (*mcomp)(Monomial,Monomial);

  min = 0; max = len-1;
  mcomp = CurrentRing->mcomp;
  while ( max > min ) {
    mid = (min+max)/2;
    c = (*mcomp)(m,marray[mid]);
    if ( c == 0 ) return mid;
    else if ( c > 0 )
      max = mid-1;
    else
      min = mid+1;
  }
  return min; 
}

void poly_to_sparse_vector(Poly p,Monomial *marray,int len)
{
  for ( ; p != 0; p = p->next )
    p->m = (Monomial)find_pos(p->m,marray,len);
}

void lrem_poly_mpz(mpz_t *v,int len,Node redlist)
{
  Node t;
  int hp,i,hsize,hsize2;
  mpz_t c1,c2,gcd;
  Poly red,s;

  hsize = bitsize_vector_mpz(v,len);
  mpz_init(c1); mpz_init(c2); mpz_init(gcd);
  for ( t = redlist; t != 0; t = t->next ) {
    red = (Poly)t->body;
    hp = (LONG)red->m;
    if ( mpz_sgn(v[hp])!= 0 ) {
      mpz_gcd(gcd,v[hp],red->c.z);
      mpz_divexact(c1,red->c.z,gcd);
      mpz_divexact(c2,v[hp],gcd); mpz_neg(c2,c2);
      // v <- c1*v-c2*red
      if ( mpz_cmp_si(c1,1) == 0 )
        ;
      else if ( mpz_cmp_si(c1,-1) == 0 ) {
        for ( i = 0; i < len; i++ )
          if ( mpz_sgn(v[i]) != 0 ) mpz_neg(v[i],v[i]);
      } else {
        for ( i = 0; i < len; i++ )
          if ( mpz_sgn(v[i]) != 0 ) mpz_mul(v[i],v[i],c1);
       }
      for ( s = red; s != 0; s = s->next ) {
        mpz_addmul(v[(LONG)s->m],s->c.z,c2);
      }
#if 0
      hsize2 = bitsize_vector_mpz(v,len);
      if ( hsize2 > 2*hsize ) {
        removecont_vector_mpz(v,len);
        hsize = bitsize_vector_mpz(v,len);
      }
#endif
    }
  }
  removecont_vector_mpz(v,len);
}

// for p < 2^31
// reducers are assumed to be monic
void lrem_poly_ff(Coef *v,int len,Node redlist)
{
  Node t;
  int hp,i;
  Coef c;
  LONG mod;
  Poly red,s;

  mod = CurrentRing->chr;
  if ( mod < 32768 ) {
    for ( t = redlist; t != 0; t = t->next ) {
      red = (Poly)t->body;
      hp = (LONG)red->m;
      v[hp].f %= mod;
      if ( v[hp].f != 0 ) {
        c.f = v[hp].f;
        for ( s = red; s != 0; s = s->next )
          v[(LONG)s->m].f -= c.f*s->c.f;
      } 
    }
    for ( i = 0; i < len; i++ ) {
      v[i].f %= mod;
      if ( v[i].f < 0 ) v[i].f += mod;
    }
  } else {
    for ( t = redlist; t != 0; t = t->next ) {
      red = (Poly)t->body;
      hp = (LONG)red->m;
      if ( v[hp].f != 0 ) {
        c = v[hp];
        for ( s = red; s != 0; s = s->next )
          v[(LONG)s->m] = mulsub_ff(v[(LONG)s->m],c,s->c);
      }
    }
  }
}

void poly_to_vector_ff(Coef *v,Poly p,Monomial *marray,int len)
{
  LONG i;
  Poly q;

  memset(v,0,len*sizeof(Coef));
  for ( q = p; q != 0; q = q->next ) {
    i = find_pos(q->m,marray,len);
    v[i] = q->c;
  }
}

Poly vector_to_poly_ff(Coef *v,Monomial *marray,int len)
{
  struct poly root;
  int i;
  Poly p,r;
  Monomial m;

  r = &root;
  for ( i = 0; i < len; i++ ) {
    if ( v[i].f != 0 ) {
      m = dup_monomial(marray[i]);
      APPENDPOLY(r,p,v[i],m);
    }
  }
  r->next = 0;
  return root.next;
}

void poly_to_vector_mpz(mpz_t *v,Poly p,Monomial *marray,int len)
{
  LONG i;
  Poly q;

  for ( i = 0; i < len; i++ ) mpz_init_set_ui(v[i],0);
  for ( q = p; q != 0; q = q->next ) {
    i = find_pos(q->m,marray,len);
    mpz_set(v[i],q->c.z);
  }
}

Poly vector_to_poly_mpz(mpz_t *v,Monomial *marray,int len)
{
  struct poly root;
  int i;
  Poly p,r;
  Coef c;
  Monomial m;

  r = &root;
  for ( i = 0; i < len; i++ ) {
    if ( mpz_sgn(v[i]) != 0 ) {
      c = mpztoc(v[i]);
      m = dup_monomial(marray[i]);
      APPENDPOLY(r,p,c,m);
    }
  }
  r->next = 0;
  return root.next;
}


// mlist is the list of all monomials
// return the spolys and the generated reducers 
void symbolic_preproc(Node sp,Parray a,Node *splist,Node *redlist,Node *mlist)
{
  struct node redroot,mroot,sproot;
  Node prev,cur,mprev,mcur,m,w,t;
  Poly red;
  Sugarp s;
  Sugarp *pa;
  int i,len;

  m = 0; prev = &sproot;
  for ( t = sp; t != 0; t = t->next ) {
    s = spoly((Spair)t->body);
    APPENDNODE(prev,cur,s->p);
    m = symb_merge_poly(m,s->p);
  }
  prev->next = 0; *splist = sproot.next; 

  pa = a->body; len = a->len; w = m;
  mprev = &mroot; prev = &redroot;
  while ( w != 0 ) {
    for ( i = 0; i < len; i++ )
      if ( divisible((Monomial)w->body,pa[i]->p->m) ) break;
    APPENDNODE(mprev,mcur,w->body);
    if ( i < len ) {
      red = reducer((Monomial)w->body,pa[i]->p);
      APPENDNODE(prev,cur,red);
      w = symb_merge_poly(w,red);
    }
    w = w->next;
  }
  prev->next = 0; mprev->next = 0;
  *redlist = redroot.next; *mlist = mroot.next;
}

Poly itop(char *n)
{
  Poly r;
  Monomial m;
  Coef c;

  c = CurrentRing->ntoc(n);
  if ( CurrentRing->zeroc(c) ) return 0;
  else {
    NEWPOLY(r);
    r->c = c;
    NEWMONOMIAL(m);
    m->td = 0;
    r->m = m;
    return r;
  }
}

Poly vtop(char *v)
{
  int nv,i,wpos,bpos,shift;
  char **vname;
  Poly r;
  Monomial m;

  nv = CurrentRing->nv;
  vname = CurrentRing->vname;

  for ( i = 0; i < nv; i++ )
    if ( !strcmp(v,vname[i]) ) break;
  if ( i == nv ) return 0;
  if ( CurrentRing->rev ) i = nv-1-i;
  NEWPOLY(r);
  NEWMONOMIAL(m);
  m->td = 1;
  bpos = i*CurrentRing->bpe;
  wpos = bpos/8; shift = 8-CurrentRing->bpe-(bpos%8);
  m->exp[wpos] = ((ULONG)1)<<(shift*8);
  r->c = CurrentRing->one;
  r->m = m;
  r->next = 0;
  return r;
}

// bpe = byte per an exponent; 1,2,4,8
Ring create_ring(Node vars,int type,int bpe,ULONG chr)
{
  Ring r;
  int i;
  Node p;

  NEWRING(r);
  r->nv = length(vars);
  r->vname = (char **)GC_malloc(r->nv*sizeof(char *));
  for ( p = vars, i = 0; p; p = p->next, i++ )
    r->vname[i] = (char *)p->body;
  switch ( bpe ) {
    case 1: r->sb = SB1; break; 
    case 2: r->sb = SB2; break; 
    case 4: r->sb = SB4; break;
    case 8: r->sb = SB8; break; 
    default: return 0; break;
  }
  r->bpe = bpe;
  r->wpe = (r->nv*bpe+7)/8;
  r->chr = chr;
  switch ( type ) {
    case 0: // grevlex
      r->graded = 1; r->rev = 1; r->mcomp = mcomp_simple;
      break;
    case 1: // glex
      r->graded = 1; r->rev = 0; r->mcomp = mcomp_simple;
      break;
    case 2: // lex
      r->graded = 0; r->rev = 0; r->mcomp = mcomp_simple;
      break;
    default:
      r = 0;
      break;
  }
  if ( chr == 0 ) {
    r->addc = add_z; r->subc = sub_z; r->mulc = mul_z; r->divc = 0;
    r->negc = neg_z; r->one = one_z(); r->zeroc = zero_z;
    r->ntoc = ntoc_z; r->printc = print_z;
  } else if ( chr == 1 ) {
    r->addc = add_q; r->subc = sub_q; r->mulc = mul_q; r->divc = div_q;
    r->negc = neg_q; r->one = one_q(); r->zeroc = zero_q;
    r->ntoc = ntoc_q; r->printc = print_q;
  } else {
    r->addc = add_ff; r->subc = sub_ff; r->mulc = mul_ff; r->divc = div_ff;
    r->negc = neg_ff; r->one = one_ff(); r->zeroc = zero_ff;
    r->ntoc = ntoc_ff; r->printc = print_ff;
  }
  return r;      
}

FILE *Input;

int skipspace() {
  int c;

  for ( c = getc(Input); ; )
    switch ( c ) {
      case ' ': case '\t': case '\r': case '\n':
        c = getc(Input);
        break;
      default:
        return c;
         break;
    }
}

void print_mpz_mat(mpz_t **mat,int row,int col)
{
  int i,j;
  Coef z;

  for ( i = 0; i < row; i++ ) {
    for ( j = 0; j < col; j++ ) {
      z.z = mat[i][j];
      CurrentRing->printc(z);
      printf(" ");
    }
    printf("\n");
  }
}

void print_mat(Coef **mat,int row,int col)
{
  int i,j;

  for ( i = 0; i < row; i++ ) {
    for ( j = 0; j < col; j++ ) {
      CurrentRing->printc(mat[i][j]);
      printf(" ");
    }
    printf("\n");
  }
}

void print_lmat(LONG **mat,int row,int col)
{
  int i,j;

  for ( i = 0; i < row; i++ ) {
    for ( j = 0; j < col; j++ ) {
      printf("%lld ",mat[i][j]);
    }
    printf("\n");
  }
}

void print_monomial(Monomial m)
{
  ULONG mask,e;
  int nv,bpe,rev,i,shift,bpos,wpos,first=1;
  char **v;

  nv = CurrentRing->nv; bpe = CurrentRing->bpe;
  v = CurrentRing->vname; rev = CurrentRing->rev;
  if ( bpe == 8 ) mask = ~0;
  else mask = (((ULONG)1)<<(bpe*8))-1;
  for ( i = 0; i < nv; i++ ) {
    bpos = rev ? (nv-i-1)*bpe : i*bpe; 
    wpos = bpos/8; shift = 8-bpe-(bpos%8);
    e = (m->exp[wpos] >> (shift*8))&mask;
    if ( e != 0 ) {
      if ( first ) first = 0;
      else printf("*");
      printf("%s",v[i]);
      if ( e > 1 ) printf("^%lld",e);
    }
  }
}

void print_poly(Poly p)
{
  Poly q;

  if ( p == 0 ) {
    printf("0");
    return;
  }
  for ( q = p; q != 0; q = q->next ) {
    printf("+("); CurrentRing->printc(q->c); printf(")");
    if ( q->m->td != 0 ) {
      putchar('*'); print_monomial(q->m);
    }
  }
}

void print_sparse_vector(Poly p)
{
  Poly q;

  for ( q = p; q != 0; q = q->next ) {
    putchar('+');
    CurrentRing->printc(q->c);
    printf("*(%lld)",(LONG)q->m);
  }
  printf("\n");
}

void print_mnode(Node p)
{
  Node q;

  for ( q = p; q != 0; q = q->next ) {
    putchar('+');
    print_monomial((Monomial)q->body);
  }
}

Spair create_spair(int i1,int i2)
{
  Spair sp;
  Sugarp p1,p2;
  Monomial m1,m2;
  LONG s1,s2,ltd;

  NEWSPAIR(sp);
  sp->i1 = i1; sp->i2 = i2;
  p1 = gbarray.body[i1];
  p2 = gbarray.body[i2];
  m1 = p1->p->m;
  m2 = p2->p->m;
  sp->lcm = lcm_monomial(m1,m2);
  ltd = sp->lcm->td;
  s1 = p1->sugar+(ltd - m1->td);
  s2 = p2->sugar+(ltd - m2->td);
  if ( s1 > s2 ) sp->sugar = s1;
  else sp->sugar = s2;
  return sp;
}

int comp_spair(Spair sa,Spair sb)
{
  if ( sa->sugar > sb->sugar ) return 1;
  if ( sa->sugar < sb->sugar ) return -1;
  return CurrentRing->mcomp(sa->lcm,sb->lcm);
}

Node insert_spair(Node l,Spair s)
{
  struct node root;
  Node cur,prev,r;

  root.next = cur = l;
  prev = &root;
  for ( ; cur != 0; prev = cur, cur = cur->next )
    if ( comp_spair(s,(Spair)cur->body) <= 0 )
      break;
  NEWNODE(r); r->body = (void *)s; r->next = cur;
  prev->next = r;
  return root.next;
}

void init_gbarray(Node base)
{
  int len,i,ishomo;
  Node b;
  Sugarp s;

  gbarray.len = len = length(base);
  gbarray.max = 2*len;
  gbarray.body = (Sugarp *)GC_malloc(gbarray.max*sizeof(Sugarp));
  ishomo = 1;
  for ( i = 0, b = base; i < len; b = b->next, i++ ) {
//    printf("poly %d=",i); print_poly((Poly)b->body); printf("\n");
    if ( !ishomo_poly((Poly)b->body) ) ishomo = 0;
    NEWSUGARP(s); 
    s->p = (Poly)b->body;
    s->sugar = tdeg_poly(s->p);
    s->p = monic_poly(s->p);
    gbarray.body[i] = s;
  }
  gbarray.ishomo = ishomo;
}

// remove the content if the coefficient ring is Z
Poly monic_poly(Poly p)
{
  if ( CurrentRing->chr == 0 )
    return removecont_poly_z(p);
  else if ( CurrentRing->chr == 1 )
    return mulc_poly(div_q(CurrentRing->one,p->c),p);
  else
    return mulc_poly(inv_ff(p->c),p);
}

void add_to_gbarray(Sugarp s,int f4)
{
  clock_t t0;
  if ( gbarray.len == gbarray.max ) {
    gbarray.max *= 2;
    gbarray.body = (Sugarp *)GC_realloc(gbarray.body,gbarray.max*sizeof(Sugarp));
  }
  s->p = monic_poly(s->p);
  if ( f4 == 0 && gbarray.ishomo != 0 ) {
    struct parray a;
    Sugarp ss;
    int i,len = gbarray.len;

    a.body = &s;
    a.max = a.len = a.ishomo = 1;
    for ( i = 0; i <= len; i++ )
      if ( gbarray.body[i] != 0 && gbarray.body[i]->p->m->td >= s->p->m->td ) {
        if ( CurrentRing->chr != 0 ) 
          gbarray.body[i] = rem_poly_sugar(gbarray.body[i],&a);
        else {
          ss = rem_poly_sugar_z(gbarray.body[i],&a);
          ss->p = removecont_poly_z(ss->p);
          gbarray.body[i] = ss;
        }
      }
  }
  gbarray.body[gbarray.len] = s;
  gbarray.len++;
}

Node update_pairs(Node d,int m)
{
  static Monomial *lcm = 0;
  static int *nouse = 0;
  static int lcmlen = 0;
  Spair sp;
  Sugarp *pa;
  struct node root;
  Node cur,prev;
  int i,k;

  if ( lcmlen < m ) {
    lcmlen = 2*m;
    lcm = (Monomial *)GC_malloc(lcmlen*sizeof(Monomial));
    nouse = (int *)GC_malloc(lcmlen*sizeof(int));
  }
  memset(nouse,0,lcmlen*sizeof(int));
  pa = gbarray.body;
  for ( i = 0; i < m; i++ )
    lcm[i] = lcm_monomial(pa[i]->p->m,pa[m]->p->m);
  // check F_k(i,m) for k=0,...,i
  // remove lcm[i] if lcm[i]=lcm[k] for some k<i
  for ( k = 0; k < m; k++ )
    for ( i = k+1; i < m; i++ )
      if ( !nouse[i] && eq_monomial(lcm[k],lcm[i]) ) { criF++; nouse[i] = 1; }
  // check M_k(i,m) for k=0,...,m-1 (k neq i)
  for ( i = 0; i < m; i++ )
    for ( k = 0; k < m; k++ )
      if ( !nouse[i] && k != i
        && divisible(lcm[i],pa[k]->p->m)
        && !eq_monomial(lcm[k],lcm[i]) )
        { criM++; nouse[i] = 1; }
  // check the disjoint criterion
  for ( i = 0; i < m; i++ )
     if ( !nouse[i] && relprime_monomial(lcm[i],pa[i]->p->m,pa[m]->p->m) )
        { criD++; nouse[i] = 1; }
  // check B_m(i,j) for i,j < m
  root.next = cur = d;
  prev = &root;
  for ( ; cur != 0; cur = cur->next ) {
    // remove cur if LM(pa[m])|cur and cur neq lcm[i] and cur neq lcm[j]
    sp = (Spair)cur->body;
    if ( divisible(sp->lcm,pa[m]->p->m) 
      && !eq_monomial(sp->lcm,lcm[sp->i1]) 
      && !eq_monomial(sp->lcm,lcm[sp->i2]) ) {
      criB++;
      prev->next = cur->next;
    } else
      prev = cur; 
  }
  d = root.next;

  for ( i = 0; i < m; i++ )
    if ( nouse[i] == 0 ) {
      sp = create_spair(i,m);
      d = insert_spair(d,sp);
    }
  return d;
}

Node init_pairs() {
  int len,i;
  Node splist;

  len = gbarray.len;
  splist = 0;
  for ( i = 1; i < len; i++ )
    splist = update_pairs(splist,i);
  return splist;
}

Node improved_buchbgerger(Node b)
{
  int i,len;
  Spair sp;
  Node t,d,gblist;
  Sugarp s,r;
  LONG sugar;
  clock_t t0;
	
	t0 = clock();
  criB = criF = criM = criD = 0;
  init_gbarray(b);
  d = init_pairs();

  sugar = 0;
  while ( d != 0 ) {
    sp = (Spair)d->body; d = d->next;
    if ( sugar != sp->sugar ) {
      printf("%lld",sp->sugar); fflush(stdout);
      sugar = sp->sugar;
    }
    s = spoly(sp);
    r = rem_poly_sugar(s,&gbarray);
    if ( r->p != 0 ) {
      len = gbarray.len;
      printf("(%d)",len); fflush(stdout);
      add_to_gbarray(r,0); // 0 indicates buchberger
      d = update_pairs(d,len);
    } else {
      printf("."); fflush(stdout);
    }
  }
  for ( gblist = 0, i = gbarray.len-1; i >= 0; i-- ) {
    CONSNODE(gblist,t,gbarray.body[i]);
  }
  
  t0 = clock() - t0;
  printf("\nF=%d,M=%d,B=%d,D=%d\n",criF,criM,criB,criD);
  printf("time=%.3fsec\n",(double)t0/(double)CLOCKS_PER_SEC);
  return gblist;
}

Node improved_buchbgerger_z(Node base)
{
  int i,len;
  Spair sp;
  Node t,splist,gblist;
  Sugarp s,r;
  LONG sugar,sugar1;

  criB = criF = criM = criD = 0;
  init_gbarray(base);
  splist = init_pairs();

  sugar = 0;
  while ( splist != 0 ) {
    sp = (Spair)splist->body; splist = splist->next;
    if ( sugar != sp->sugar ) {
      printf("%lld",sp->sugar); fflush(stdout);
      sugar = sp->sugar;
    }
    s = spoly(sp);
    r = rem_poly_sugar_z(s,&gbarray);
    if ( r->p != 0 ) {
      len = gbarray.len;
      printf("(%d)",len); fflush(stdout);
      add_to_gbarray(r,0); // 0 indicates buchberger 
      splist = update_pairs(splist,len);
    } else {
      printf("."); fflush(stdout);
    }
  }
  for ( gblist = 0, i = gbarray.len-1; i >= 0; i-- ) {
     NEWNODE(t); t->body=(void *)gbarray.body[i];
    t->next = gblist; gblist = t;
  }
  printf("F=%d,M=%d,B=%d,D=%d\n",criF,criM,criB,criD);
  return gblist;
}

LONG mulmod_64(LONG a,LONG b,LONG m)
{
  mp_limb_t d[2],q[2];
  mp_limb_t r;

  d[1] = (mp_limb_t)mpn_mul_1(d,(mp_limb_t *)&a,1,(mp_limb_t)b);
  r = (mp_limb_t)mpn_divmod_1((mp_limb_t *)q,(mp_limb_t *)d,2,(mp_limb_t)m);
  return (LONG)r;
}

// (c-a*b) mod m
LONG mulsubmod_64(LONG c,LONG a,LONG b,LONG m)
{
  LONG l;

  l = (c-mulmod_64(a,b,m))%m;
  if ( l < 0 ) l += m;
  return l;
}

LONG inv_64(LONG s,LONG m)
{
  LONG f1,f2,a1,a2,q,r;

  f1 = s; f2 = m;
  for ( a1 = 1, a2 = 0; ; ) {
    q = f1/f2; r = f1 - f2*q; f1 = f2; f2 = r;
    if ( r == 0 ) 
      break;
    r = mulmod_64(a2,q,m);
    r = a1-r;
    if ( r < 0 ) r += m;
    a1 = a2; a2 = r;
  }
  return a2;
}

LONG **alloc_LONG_mat(int row,int col)
{
  LONG **mat;
  int i;

  mat = (LONG **)GC_malloc(row*sizeof(LONG *));
  for ( i = 0; i < row; i++ )
    mat[i] = (LONG *)GC_malloc(col*sizeof(LONG));
  return mat;
}

mpz_t *alloc_mpz_vector(int len)
{
  mpz_t *v;
  int i;

  v = (mpz_t *)GC_malloc(len*sizeof(mpz_t));
  for ( i = 0; i < len; i++ ) mpz_init_set_ui(v[i],0);
  return v;
}

mpz_t **alloc_mpz_mat(int row,int col)
{
  mpz_t **mat;
  int i;

  mat = (mpz_t **)GC_malloc(row*sizeof(mpz_t *));
  for ( i = 0; i < row; i++ ) mat[i] = alloc_mpz_vector(col);
  return mat;
}

void red_by_vector_64(LONG *p,LONG *r,int len,LONG mod)
{
  LONG h;

  h = *p;
  *p = 0; p++; r++; len--;
  for ( ; len; len--, r++, p++ ) {
    if ( *r != 0 ) {
      *p = mulsubmod_64(*p,*r,h,mod);
    }
  }
}

int rref_64(LONG **mat,int row,int col,LONG mod,int *colstat)
{
  int i,j,k,l,rank;
  LONG inv,a;
  LONG *t,*pivot,*pk;

  memset(colstat,0,col*sizeof(int));
  for ( rank = 0, j = 0; j < col; j++ ) {
    for ( i = rank; i < row; i++ )
      if ( mat[i][j] != 0 )
        break;
    if ( i == row ) {
      colstat[j] = 0;
      continue;
    } else
      colstat[j] = 1;
    if ( i != rank ) {
      t = mat[i]; mat[i] = mat[rank]; mat[rank] = t;
    }
    pivot = mat[rank];
    inv = inv_64(pivot[j],mod);
    for ( k = j, pk = pivot+k; k < col; k++, pk++ )
      if ( pk[0] != 0 )
        *pk = mulmod_64(*pk,inv,mod);
    for ( i = rank+1; i < row; i++ )
      if ( mat[i][j] != 0 )
        red_by_vector_64(mat[i]+j,pivot+j,col-j,mod);
    rank++;
  }
  for ( j = col-1, l = rank-1; j >= 0; j-- )
    if ( colstat[j] ) {
      pivot = mat[l];
      for ( i = 0; i < l; i++ )
        if ( mat[i][j] != 0 )
          red_by_vector_64(mat[i]+j,pivot+j,col-j,mod);
      l--;
    }
  return rank;
}

void red_by_vector_ff(Coef *p,Coef *r,int len)
{
  Coef h,c;

  h = *p;
  p->f = 0; p++; r++; len--;
  for ( ; len; len--, r++, p++ ) {
    if ( r->f != 0 ) {
      *p = mulsub_ff(*p,*r,h);
    }
  }
}

// for mod < 2^31
int rref_ff(Coef **mat,int row,int col,int *colstat)
{
  int i,j,k,l,rank;
  Coef a;
  Coef *t,*pivot,*pk;
  Coef c,inv;

  memset(colstat,0,col*sizeof(int));
  for ( rank = 0, j = 0; j < col; j++ ) {
    for ( i = rank; i < row; i++ )
      if ( mat[i][j].f != 0 )
        break;
    if ( i == row ) {
      colstat[j] = 0;
      continue;
    } else
      colstat[j] = 1;
    if ( i != rank ) {
      t = mat[i]; mat[i] = mat[rank]; mat[rank] = t;
    }
    pivot = mat[rank];
    c = pivot[j]; 
    inv = inv_ff(c);
    for ( k = j, pk = pivot+k; k < col; k++, pk++ )
      if ( pk[0].f != 0 )
        *pk = mul_ff(*pk,inv);
    for ( i = rank+1; i < row; i++ )
      if ( mat[i][j].f != 0 )
        red_by_vector_ff(mat[i]+j,pivot+j,col-j);
    rank++;
  }
  for ( j = col-1, l = rank-1; j >= 0; j-- )
    if ( colstat[j] ) {
      pivot = mat[l];
      for ( i = 0; i < l; i++ )
        if ( mat[i][j].f != 0 )
          red_by_vector_ff(mat[i]+j,pivot+j,col-j);
      l--;
    }
  return rank;
}

int inttorat_mpz(mpz_t c,mpz_t m,mpz_t b,mpz_t nm,mpz_t dn)
{
  mpz_t u1,v1,u2,v2,r1,r2;
  mpz_t q,t;

  mpz_init_set_ui(u1,0); mpz_init_set_ui(v1,1);
  mpz_init_set(u2,m); mpz_init_set(v2,c);
  mpz_init(q); mpz_init(t); mpz_init(r1); mpz_init(r2);
  while ( mpz_cmp(v2,b) >= 0 ) {
    /* r2 = u2-q*v2 */
    mpz_fdiv_qr(q,r2,u2,v2);
    mpz_set(u2,v2); mpz_set(v2,r2);
    /* r1 = u1-q*v1 */
    mpz_mul(t,q,v1); mpz_sub(r1,u1,t);
    mpz_set(u1,v1); mpz_set(v1,r1);
  }
  if ( mpz_cmp(v1,b) >= 0 ) return 0;
  else {
    mpz_gcd(t,v1,v2);
    if ( mpz_cmp_si(t,1) == 0 )
      mpz_set_ui(r1,0); 
    else {
      /* v1 /= t, v2 /= t, t=c*v1-v2, r1=t%m */
      mpz_divexact(v1,v1,t); mpz_divexact(v2,v2,t);
      mpz_mul(t,c,v1); mpz_sub(t,t,v2); mpz_mod(r1,t,m);
    }
    if ( mpz_sgn(r1) ) return 0;
    if ( mpz_sgn(v1)<0  ) {
      mpz_neg(dn,v1); mpz_neg(nm,v2);
    } else {
     mpz_set(dn,v1); mpz_set(nm,v2);
    }
    return 1;
  }
}

int intmtoratm_mpz(mpz_t **mat,int row,int col,mpz_t md,mpz_t **nm,mpz_t dn)
{
  mpz_t t,s,b,u,nm1,dn1;
  int i,j,k,l,ret;
  mpz_t *mi,*nmk;

  if ( mpz_cmp_si(md,1) == 0 )
    return 0;
  mpz_init(t); mpz_init(s); mpz_init(b); mpz_init(u);
  mpz_init(nm1); mpz_init(dn1);
  mpz_fdiv_q_2exp(t,md,1); mpz_sqrt(s,t); mpz_fdiv_q_2exp(b,s,16);
  if ( !mpz_sgn(b) ) mpz_set_ui(b,1);
  mpz_set_ui(dn,1);
  for ( i = 0; i < row; i++ )
    for ( j = 0, mi = mat[i]; j < col; j++ )
      if ( mpz_sgn(mi[j]) ) {
        mpz_mul(s,mi[j],dn);
        mpz_mod(u,s,md);
        ret = inttorat_mpz(u,md,b,nm1,dn1);
        if ( !ret ) 
          return 0;
        else {
          if ( mpz_cmp_si(dn1,1) != 0 ) {
            for ( k = 0; k < i; k++ )
              for ( l = 0, nmk = nm[k]; l < col; l++ ) mpz_mul(nmk[l],nmk[l],dn1);
            for ( l = 0, nmk = nm[i]; l < j; l++ ) mpz_mul(nmk[l],nmk[l],dn1);
          }
          mpz_set(nm[i][j],nm1);
          mpz_mul(dn,dn,dn1);
        }
      }
  return 1;
}

int rref_check_mpz(mpz_t **mat,int row,int col,mpz_t **nm,mpz_t dn,int rank,int clen,int *rind,int *cind)
{
  int i,j,k,l;
  mpz_t t;
  mpz_t *w;
  mpz_t *mati;
  mpz_t *nmk;

  w = (mpz_t *)GC_malloc(clen*sizeof(mpz_t));
  mpz_init(t);
  for ( i = 0; i < clen; i++ ) mpz_init(w[i]);
  for ( i = 0; i < row; i++ ) {
    mati = mat[i];
    for ( l = 0; l < clen; l++ ) mpz_set_ui(w[l],0);
    for ( k = 0; k < rank; k++ )
      for ( l = 0, nmk = (mpz_t *)nm[k]; l < clen; l++ ) {
        /* w[l] += mati[rind[k]]*nmk[k] */
        if ( mpz_sgn(mati[rind[k]]) != 0 ) mpz_addmul(w[l],mati[rind[k]],nmk[l]);
      }
    for ( j = 0; j < clen; j++ ) {
      if ( mpz_sgn(mati[cind[j]]) != 0 ) mpz_mul(t,dn,mati[cind[j]]);
      else mpz_set_ui(t,0);
      if ( mpz_cmp(w[j],t) ) break;
    }
    if ( j != clen ) break;
  }
  if ( i != row ) return 0;
  else return 1;
}

int rref_mpz(mpz_t **mat,int row,int col)
{
  mpz_t *mi;
  LONG **wmat;
  LONG *wmi;
  mp_limb_t md,inv,t,t1;
  mpz_t **tmat,**num;
  mpz_t *tmi;
  mpz_t den;
  mpz_t q,m1,m3,s,u;
  int *colstat,*wcolstat,*rind,*cind;
  int ind,i,j,k,l,rank,rank0;
  int ret;

  wmat = (LONG **)alloc_LONG_mat(row,col);
  colstat = (int *)GC_malloc(col*sizeof(int));
  wcolstat = (int *)GC_malloc(col*sizeof(int));
  mpz_init(m1); mpz_init(m3); mpz_init(den);
  for ( ind = 0; ; ind++ ) {
    fprintf(stderr,".");
    md = get_prime64(ind);
    if ( md == 0 ) 
      error("prime64 : exshausted");
    for ( i = 0; i < row; i++ )
      for ( j = 0, mi = mat[i], wmi = wmat[i]; j < col; j++ )
        wmi[j] = mpz_fdiv_ui(mi[j],md);
    rank = rref_64(wmat,row,col,md,wcolstat);
    if ( ind == 0 ) {
RESET:
      mpz_set_ui(m1,md);
      rank0 = rank;
      memcpy(colstat,wcolstat,col*sizeof(int));
      // crmat
      tmat = (mpz_t **)alloc_mpz_mat(rank,col-rank);
      // 
      num = (mpz_t **)alloc_mpz_mat(rank,col-rank);
      for ( i = 0; i < rank; i++ )
        for ( j = k = 0, tmi = tmat[i], wmi = wmat[i]; j < col; j++ )
          if ( !colstat[j] ) { mpz_set_ui(tmi[k],wmi[j]); k++; }
    } else if ( rank < rank0 ) {
      fprintf(stderr,"lower rank matrix; continuing...\n");
      continue;
    } else if ( rank > rank0 ) {
      fprintf(stderr,"higher rank matrix; resetting...\n");
      goto RESET;
    } else {
      for ( j = 0; (j<col) && (colstat[j]==wcolstat[j]); j++ );
      if ( j < col ) {
        fprintf(stderr,"inconsitent colstat; resetting...\n");
        goto RESET;
      } else {
        inv = inv_64(mpz_fdiv_ui(m1,md),md);
        mpz_mul_ui(m3,m1,md);
        // CRT
        for ( i = 0; i < rank; i++ )      
          for ( j = k = 0, tmi = tmat[i], wmi = wmat[i]; j < col; j++ )
            if ( !colstat[j] ) {
              if ( mpz_sgn(tmi[k]) ) {
              /* f3 = f1+m1*(m1 mod md)^(-1)*(f2 - f1 mod md) */
                t = mpz_fdiv_ui(tmi[k],md);
                if ( wmi[j] >= t ) t = wmi[j]-t;
                else t = md-(t-wmi[j]);
                mpz_addmul_ui(tmi[k],m1,mulmod_64(t,inv,md));
              } else if ( wmi[j] ) {
              /* f3 = m1*(m1 mod m2)^(-1)*f2 */
                mpz_mul_ui(tmi[k],m1,mulmod_64(wmi[j],inv,md));
              }
              k++;
            }
        mpz_set(m1,m3);
        // inttorat
        if ( ind % 4 )
          ret = 0;
        else 
          ret = intmtoratm_mpz(tmat,rank,col-rank,m1,num,den);
        if ( ret ) {
          rind = (int *)GC_malloc(rank*sizeof(int));
          cind = (int *)GC_malloc((col-rank)*sizeof(int));
           // colstat[i] = 1 for i=i1,....,il => k-th row= den*e(ik)+...
          for ( j = k = l = 0; j < col; j++ )
            if ( colstat[j] ) rind[k++] = j;  
            else cind[l++] = j;
          if ( rref_check_mpz(mat,row,col,num,den,rank,col-rank,rind,cind) ) {
            for ( i = 0; i < rank; i++ ) {
              for ( j = 0; j < col; j++ ) mpz_set_ui(mat[i][j],0);
              mpz_set(mat[i][rind[i]],den);
              for ( j = 0; j < col-rank; j++ )
                mpz_set(mat[i][cind[j]],num[i][j]);
            }
            return rank;
          }
        }
      }
    }
  }
}

clock_t Tsymb,Trref,Tadd;

Node f4_reduction_ff(Node sp)
{
  int row,col,i,j,k,rank,nsp,nred,nrsp,nrcol;
  Coef **mat;
  Coef *v;
  Monomial *marray,*rmarray;
  Sugarp s;
  struct node root;
  Node splist,redlist,mlist;
  Node t,r,nd;
  int *harray,*colstat;
  clock_t t0,t1;

  t0 = clock();
  symbolic_preproc(sp,&gbarray,&splist,&redlist,&mlist);
  t0 = clock()-t0; Tsymb += t0; 

  nsp = length(splist);
  nred = length(redlist);
  row = nsp+nred;
  col = length(mlist);
  marray = (Monomial *)GC_malloc(col*sizeof(Monomial));
  harray = (int *)GC_malloc(col*sizeof(int));
  for ( i = 0, t = mlist; i < col; i++, t = t->next )
    marray[i] = (Monomial)t->body;
  for ( t = redlist; t != 0; t = t->next ) {
    poly_to_sparse_vector((Poly)t->body,marray,col);
    harray[(LONG)(((Poly)t->body)->m)] = 1;
  }
  mat = (Coef **)GC_malloc(row*sizeof(Coef *));
  // number of remaining cols
  nrcol = col-nred;
  // reduced marray
  rmarray = (Monomial *)GC_malloc(nrcol*sizeof(Monomial));
  for ( j = k = 0; j < col; j++ )
    if ( harray[j] == 0 ) rmarray[k++] = marray[j];
  fprintf(stderr,"elim1...");
  t0 = clock();
  v = (Coef *)GC_malloc(col*sizeof(Coef));
  for ( t = splist, i = 0; t != 0; t = t->next ) {
//    print_poly(t->body); printf("\n");
    poly_to_vector_ff(v,(Poly)t->body,marray,col);
    lrem_poly_ff(v,col,redlist);
    for ( j = 0; j < col && v[j].f == 0; j++ );
    if ( j < col ) {
      mat[i] = (Coef *)GC_malloc(nrcol*sizeof(Coef));
      for ( j = k = 0; j < col; j++ )
        if ( harray[j] == 0 ) mat[i][k++] = v[j];
      i++;
    }
  }
  t0 = clock()-t0;
  fprintf(stderr," %.3fsec ",(double)t0/(double)CLOCKS_PER_SEC);
  // number of reduced nonzero sp
  nrsp = i;
  t0 = clock();
  fprintf(stderr,"%dx%d...",nrsp,nrcol);
  colstat = (int *)GC_malloc(nrcol*sizeof(int));
  rank = rref_ff(mat,nrsp,nrcol,colstat);
  t0 = clock()-t0;
  fprintf(stderr," %.3fsec new: %d\n",(double)t0/(double)CLOCKS_PER_SEC,rank);
  r = &root;
  for ( i = 0; i < rank; i++ ) {
    NEWSUGARP(s);
    s->p = vector_to_poly_ff(mat[i],rmarray,nrcol);
    s->sugar = tdeg_poly(s->p);
    APPENDNODE(r,nd,s);
  }
  r->next = 0;
  return root.next;
}

Node f4_reduction_z(Node sp)
{
  int row,col,i,j,k,rank,nsp,nred,nrsp,nrcol;
  mpz_t **mat;
  mpz_t *v;
  Monomial *marray,*rmarray;
  Sugarp s;
  struct node root;
  Node t,r,nd;
  Node splist,redlist,mlist;
  int *harray;
  clock_t t0,t1;

  t0 = clock();
  symbolic_preproc(sp,&gbarray,&splist,&redlist,&mlist);
  t0 = clock()-t0; Tsymb += t0; 

  nsp = length(splist);
  nred = length(redlist);
  row = nsp+nred;
  col = length(mlist);
  marray = (Monomial *)GC_malloc(col*sizeof(Monomial));
  harray = (int *)GC_malloc(col*sizeof(int));
  for ( i = 0, t = mlist; i < col; i++, t = t->next )
    marray[i] = (Monomial)t->body;
  v = (mpz_t *)GC_malloc(col*sizeof(mpz_t));
  for ( t = redlist; t != 0; t = t->next ) {
    poly_to_sparse_vector((Poly)t->body,marray,col);
    harray[(LONG)(((Poly)t->body)->m)] = 1;
  }
  mat = (mpz_t **)GC_malloc(row*sizeof(mpz_t *));
  // number of remaining cols
  nrcol = col-nred;
  // reduced marray
  rmarray = (Monomial *)GC_malloc(nrcol*sizeof(Monomial));
  for ( j = k = 0; j < col; j++ )
    if ( harray[j] == 0 ) rmarray[k++] = marray[j];

  fprintf(stderr,"elim1...");
  t0 = clock();
  for ( t = splist, i = 0; t != 0; t = t->next ) {
//    print_poly(t->body); printf("\n");
    poly_to_vector_mpz(v,(Poly)t->body,marray,col);
    lrem_poly_mpz(v,col,redlist);
    for ( j = 0; j < col && mpz_sgn(v[j]) == 0; j++ );
    if ( j < col ) {
      mat[i] = (mpz_t *)GC_malloc(nrcol*sizeof(mpz_t));
      for ( k = 0; k < nrcol; k++ ) mpz_init_set_ui(mat[i][k],0);
      for ( j = k = 0; j < col; j++ )
        if ( harray[j] == 0 ) mpz_set(mat[i][k++],v[j]);
      i++;
    }
  }
  t0 = clock()-t0;
  fprintf(stderr," %.3fsec ",(double)t0/(double)CLOCKS_PER_SEC);
  // number of reduced nonzero sp
  nrsp = i;
  t0 = clock();
  fprintf(stderr,"%dx%d...",nrsp,nrcol);
  rank = rref_mpz(mat,nrsp,nrcol);
  t0 = clock()-t0;
  fprintf(stderr," %.3fsec new: %d\n",(double)t0/(double)CLOCKS_PER_SEC,rank);
  r = &root;
  for ( i = 0; i < rank; i++ ) {
    NEWSUGARP(s);
    s->p = vector_to_poly_mpz(mat[i],rmarray,nrcol);
    s->sugar = tdeg_poly(s->p);
    APPENDNODE(r,nd,s);
  }
  r->next = 0;
  return root.next;
}

Node f4(Node base)
{
  int len,i,nsp;
  Node b,sp,splist,redlist,gblist,nd,nd1,plist,nplist,mlist,t;
  LONG sugar,sugar1,mins;
  clock_t t0;

  criB = criF = criM = criD = 0;
  Tsymb = Trref = Tadd = 0;
  init_gbarray(base);
  sp = init_pairs();

  while ( sp != 0 ) {
    mins = ((Spair)sp->body)->sugar;
    nd = 0;
    while ( sp!= 0 && ((Spair)sp->body)->sugar == mins ) {
      CONSNODE(nd,nd1,sp->body);
      sp = sp->next;
    }
    fprintf(stderr,"%lld ",mins);
    t0 = clock();
    if ( CurrentRing->chr != 0 )
      nplist = f4_reduction_ff(nd);
    else
      nplist = f4_reduction_z(nd);
    t0 = clock()-t0; Trref += t0; 
    t0 = clock();
    for ( nd = nplist; nd != 0; nd = nd->next ) {
//      printf("p%d:",gbarray.len);
//      print_poly(((Sugarp)nd->body)->p); printf("\n");
      len = gbarray.len;
      add_to_gbarray((Sugarp)nd->body,1); // 1 indicates f4
      sp = update_pairs(sp,len);
    }
    t0 = clock()-t0; Tadd += t0; 
  }
  for ( gblist = 0, i = gbarray.len-1; i >= 0; i-- ) {
    CONSNODE(gblist,t,gbarray.body[i]);
  }
  fprintf(stderr,"F=%d,M=%d,B=%d,D=%d\n",criF,criM,criB,criD);
  return gblist;
}

Node get_vars()
{
  struct node root;
  Node p,p1;
  int c,i;
  char buf[BUFSIZ];
  char *s;

  p = &root;
  while ( (c = getc(Input)) != '[' );
  while ( 1 ) {
    c = skipspace();
    if ( c == ']' ) {
      p->next = 0;
      return root.next;
    } else {
      buf[0] = c;
      for ( i = 1; ; i++ ) {
        if ( i == BUFSIZ )
          error("get_vars : variable name too LONG");
        c = getc(Input);
        if ( !isalnum(c) ) {
          ungetc(c,Input);
          buf[i] = 0;
          break;
        } else
          buf[i] = c;
      }
      s = (char *)GC_malloc(i+1);
      strcpy(s,buf);
      APPENDNODE(p,p1,s);
    }
  }
}

void print_node(Node p)
{
  Node q;

  for ( q = p; q != 0; q = q->next ) {
    print_poly((Poly)q->body); printf("\n");
  }
}

void *gc_realloc(void *p,size_t osize,size_t nsize)
{
  return (void *)GC_realloc(p,nsize);
}

Node minimalize(Node g)
{
  int len,i,j,lenm;
  Node t,r;
  Sugarp *a;
  Monomial mi;

  for ( len = 0, t = g; t != 0; t = t->next, len++ );
  a = (Sugarp *)GC_malloc(len*sizeof(Sugarp));
  for ( i = 0, t = g; i < len; t = t->next, i++ ) a[i] = (Sugarp)t->body;
  for ( i = 0; i < len; i++ ) {
    if ( a[i] == 0 ) continue;
    mi = a[i]->p->m;
    for ( j = 0; j < len; j++ )
      if ( j != i && a[j] != 0 && divisible(a[j]->p->m,mi) ) {
        a[j] = 0;
      }
  }
  r = 0;
  lenm = 0;
  for ( i = len-1; i >= 0; i-- ) {
    if ( a[i] != 0 ) {
      lenm++;
      NEWNODE(t); t->body = (void *)a[i]; t->next = r; r = t;
    }
  }
  printf("%d->%d\n",len,lenm);
  return r;
}

Node interreduce(Node n)
{
  struct parray pa;
  Sugarp *a,*a1;
  int len,i,j,k;
  Node t,r;

  for ( len = 0, t = n; t != 0; t = t->next, len++ );
  a = (Sugarp *)GC_malloc(len*sizeof(Sugarp));
  for ( i = 0, t = n; i < len; t = t->next, i++ ) a[i] = (Sugarp)t->body;
  a1 = (Sugarp *)GC_malloc((len-1)*sizeof(Sugarp));
  pa.body = a1;
  pa.max = pa.len = len-1;
  pa.ishomo = 0; // don't core
  for ( i = 0; i < len; i++ ) {
    for ( j = k = 0; j < len; j++ )
      if ( j != i ) a1[k++] = a[j];
    if ( CurrentRing->chr == 0 )
      a[i] = rem_poly_sugar_z(a[i],&pa);
    else
      a[i] = rem_poly_sugar(a[i],&pa);
    a[i]->p = monic_poly(a[i]->p);
  }
  r = 0;
  for ( i = len-1; i >= 0; i-- ) {
    NEWNODE(t); t->body = (void *)a[i]; t->next = r; r = t;
  }
  return r;
}

// input file format :
// chr ordid bpe
// [x y z ...]
// p1,p2,...,pn;
////////////////////////////////// f5 //////////////////////////////
int criSY,criMG,regred,opt_d1;
clock_t TcriS,TcriM,Tred,Tregsp,Tins,Tinscomp,Tinsdo;
//criSY = criMG = regred = 0;

void print_modmonom(Modmonom a)
{
	Poly p;
	NEWPOLY(p);
	//p->c.f = 1;
	//p->c.z = 1;
	p->c = CurrentRing->one;
	p->m = a->m;
	p->next = 0;
	printf("n:%d mon:",a->basenum);
	print_poly(p);
}

void init_siggbarray(Node base)	//初期のsiggbarrayの作成
{
  int len,i,ishomo;
  Node b;
  //Sugarp s;
  Sigpoly s;
  Monomial m;
  Modmonom mm;
  
  NEWMONOMIAL(m);
	m->td = 0;
	for(i = 0; i < CurrentRing->wpe; i++){
		m->exp[i] = 0;
	}
	
  siggbarray.len = len = length(base);
  siggbarray.max = 2*len;
  siggbarray.body = (Sigpoly *)GC_malloc(siggbarray.max*sizeof(Sigpoly));
  ishomo = 1;
  for ( i = 0, b = base; i < len; b = b->next, i++ ) {
//    printf("poly %d=",i); print_poly((Poly)b->body); printf("\n");
    if ( !ishomo_poly((Poly)b->body) ) ishomo = 0;
    NEWSIGPOLY(s); 
    s->p = (Poly)b->body;
    //s->sugar = tdeg_poly(s->p);
    s->p = monic_poly(s->p);
    
    NEWMODMONOM(mm);
    mm->basenum = i;
    mm->m = m;
    if(opt_modorder == 2){
    	mm->sch = s->p->m;
    }
    s->sig = mm;
    
    siggbarray.body[i] = s;
  }
  siggbarray.ishomo = ishomo;
}

void init_syzarray(Node base)	//初期のsyzarrayの作成
{
	syzarray.len = 0;
	syzarray.max = 2*length(base);
	syzarray.body = (Modmonom *)GC_malloc(syzarray.max*sizeof(Modmonom));
}

int compare_pot(Modmonom a,Modmonom b){	//POT順序
	if(a->basenum > b->basenum){
		return 1;
	}else if(a->basenum < b->basenum){
		return -1;
	}
	return mcomp_simple(a->m,b->m);
}

int compare_top(Modmonom a,Modmonom b){	//TOP順序
	int scomp;
	scomp = mcomp_simple(a->m,b->m);
	if(scomp != 0){
		return scomp;
	}
	if(a->basenum > b->basenum){
		return 1;
	}else if(a->basenum < b->basenum){
		return -1;
	}
	return 0;
}

int compare_schreyer(Modmonom a,Modmonom b){	//Schereyer順序
	int mcomp;
	mcomp = mcomp_simple(a->sch,b->sch);
	if(mcomp != 0){
		return mcomp;
	}
	if(a->basenum > b->basenum){
		return 1;
	}else if(a->basenum < b->basenum){
		return -1;
	}
	return 0;
}

int compare_modmonom(Modmonom a,Modmonom b){	//加群単項式a,bの項順序比較。a > b => 1,a < b => -1, a = b => 0
	switch(opt_modorder){
		case 0:
			return compare_pot(a,b);
			break;
		case 1:
			return compare_top(a,b);
			break;
		case 2:
			return compare_schreyer(a,b);
			break;
	}

}

Modmonom mul_modmonom(Modmonom mod,Monomial mon)	//加群単項式と単項式の積
{
	Monomial m;
	m = mul_monomial(mon,mod->m);
	Modmonom ans;
	NEWMODMONOM(ans);
	ans->m = m;
	ans->basenum = mod->basenum;
	if(opt_modorder == 2){
		ans->sch = mul_monomial(m,siggbarray.body[ans->basenum]->p->m);
	}
	return ans;
}

Node regular_spair(int n)	//疑正則S多項式の生成
{
	Node splist,t;
	splist = 0;
	
	int i,j,flag;
	Sigspair sp;
	Monomial gm,rm,lcm,m1,m2;
	Modmonom t1,t2;
	Sigpoly g,r;
	j = 0;
	r = siggbarray.body[n];
	rm = r->p->m;
	for(i = n - 1; i >= 0; i--){
		g = siggbarray.body[i];
		gm = g->p->m;
		lcm = lcm_monomial(rm,gm);
		m1 = div_monomial(lcm,rm);
		m2 = div_monomial(lcm,gm);
		t1 = mul_modmonom(r->sig,m1);
		t2 = mul_modmonom(g->sig,m2);
		flag = compare_modmonom(t1,t2);
		if(flag != 0){
			NEWSIGSPAIR(sp);
			sp->lcm = lcm;
			sp->i1 = i;
			sp->i2 = n;
			if(flag == 1){
				sp->sig = t1;
			}else if(flag == -1){
				sp->sig = t2;
			}
			CONSNODE(splist,t,sp);
		}
	}
	return splist;
}

Poly red_poly(Poly p1,Poly p2)	//red_poly_sugarのsugar無しver
{
  Monomial m;
  Coef c;
  Poly p;
  Poly s;

  m = div_monomial(p1->m,p2->m);
  c = CurrentRing->divc(p1->c,p2->c);
  c = CurrentRing->negc(c);
  NEWPOLY(p); p->c = c; p->m = m; p->next = 0;
  NEWPOLY(s);
  s = merge_poly(p1,mul1_poly(p,p2));
  return s;
}

Sigpoly sigspoly(Sigspair sp)	//signature付きS多項式の情報からS多項式を生成
{
  Monomial lcm,m1;
  Poly q1;
  Poly p1,p2,s1;
  int i1,i2;
  Coef mul;
  Sigpoly ans;

  i1 = sp->i1;
  i2 = sp->i2;
  p1 = siggbarray.body[i1]->p;
  p2 = siggbarray.body[i2]->p;
  lcm = sp->lcm;
  m1 = div_monomial(lcm,p1->m);
  NEWPOLY(q1); q1->c = p2->c; q1->m = m1; q1->next = 0;
  NEWPOLY(s1);
  //s1->sugar = p1->sugar + m1->td;
  s1 = mul1_poly(q1,p1);
  NEWSIGPOLY(ans);
	ans->p = red_poly(s1,p2);
  //return red_poly(s1,p2);
  ans->sig = sp->sig;
  return ans;
}

int mod_divisible(Modmonom dnd,Modmonom dvr)	//加群単項式dvrが加群単項式dndを割り切る:1 割り切らない:0
{
	if(dnd->basenum != dvr->basenum){
		return 0;
	}
	return divisible(dnd->m,dvr->m);
}

int syzygy_criterion(Sigspair sp)	//割り切るsyzygyが存在する:1 しない:0
{
	clock_t t0;
	t0 = clock();
	int i;
  for(i = 0; i < syzarray.len; i++){
  	if(mod_divisible(sp->sig,syzarray.body[i]) == 1){
  		//printf("syz criterion:1\n");
  		if(opt_d1 >= 1){
	  		fprintf(stderr,"s");
	  	}
  		criSY++;
  		TcriS += clock() - t0;
  		return 1;
  	}
  }
  //printf("syz criterion:0\n");
  TcriS += clock() - t0;
  return 0;
}

void add_to_syzarray(Modmonom m)	//syzygyを追加
{
  //clock_t t0;
  if ( syzarray.len == syzarray.max ) {
    syzarray.max *= 2;
    syzarray.body = (Modmonom *)GC_realloc(syzarray.body,syzarray.max*sizeof(Modmonom));
  }
  syzarray.body[syzarray.len] = m;
  syzarray.len++;
  if(opt_d1 >= 1){
	  fprintf(stderr,".");
	}
}

int mg_criterion(Sigspair sp/*,Poly spoly*/)	//Algorithm3の8,9行目の判定
{
	clock_t t0;
	t0 = clock();
	int i,comp,flag;
	Monomial m,mg;
	Sigpoly g;
	flag = 0;
	for(i = 0; i < siggbarray.len; i++){		
		g = siggbarray.body[i];
		if(mod_divisible(sp->sig,g->sig) == 1){
			m = div_monomial(sp->sig->m,g->sig->m);
			mg = mul_monomial(m,g->p->m);
			if(mcomp_simple(sp->lcm,mg) == 1){
				if(opt_d1 >= 1){
					fprintf(stderr,"m");
				}
				criMG++;
				TcriM += clock() - t0;
				return 1;
			}
		}
	}
	TcriM += clock() - t0;
	return 0;
}
clock_t Tredp;
Sigpoly regular_reduce(Sigpoly p,Sigparray a)	//sigma_top簡約
{
	//printf("regular reduce\n");
  struct poly root;
  Poly r,x,y;
  Sigpoly s;
  Sigpoly *pa;
  int i,len;
  Monomial t;
  Modmonom sig,tsig;
  Coef mul;
  clock_t t0;

//  print_poly(p->p); printf("\n");
  r = &root;
  NEWSIGPOLY(s); *s = *p;
  s->sig = p->sig;
  pa = a->body;
  len = a->len;
  while ( s->p != 0 ) {
    for ( i = 0; i < len; i++ ) {
      if ( divisible(s->p->m,pa[i]->p->m) ){
      	t = div_monomial(s->p->m,pa[i]->p->m);
      	//tsig = mul_modmonom(s->sig,t);
      	tsig = mul_modmonom(pa[i]->sig,t);
      	if(compare_modmonom(s->sig,tsig) == 1){
	      	break;
	      }
      }
    }
    if ( i < len ) {
	  	t0 = clock();
	  	s->p = red_poly(s->p,pa[i]->p);
	  	Tredp += clock() - t0;
//      printf("->"); print_poly(s->p); printf("\n");
    } else {
      NEWPOLY(x); *x = *(s->p); r->next = x; r = x;
      s->p = s->p->next;
    }
  }
  r->next = 0;
  s->p = root.next;
  return s;
}

int length_poly(Poly p){
	Poly q;
	int ans = 0;
	for(q = p; q != 0; q = q->next){
		ans++;
	}
	return ans;
}

void add_to_siggbarray(Sigpoly s)	//siggbarrayにsを追加
{
  //clock_t t0;
  if ( siggbarray.len == siggbarray.max ) {
    siggbarray.max *= 2;
    siggbarray.body = (Sigpoly *)GC_realloc(siggbarray.body,siggbarray.max*sizeof(Sigpoly));
  }
  s->p = monic_poly(s->p);
  siggbarray.body[siggbarray.len] = s;
  siggbarray.len++;
}
/////////////10/10///////////////////////
Sigspair *regular_spair_0(int n,int *len)	//syzygy criterionも行う
{
	Sigspair *sparray;
	sparray = (Sigspair *)GC_malloc(n*sizeof(Sigspair));
	
	int i,j,flag;
	Sigspair sp;
	struct sigspair tsp;
	Monomial gm,rm,lcm,m1,m2;
	Modmonom t1,t2;
	Sigpoly g,r;
	j = 0;
	r = siggbarray.body[n];
	rm = r->p->m;
	for(i = n - 1; i >= 0; i--){
		g = siggbarray.body[i];
		gm = g->p->m;
		lcm = lcm_monomial(rm,gm);
		m1 = div_monomial(lcm,rm);
		m2 = div_monomial(lcm,gm);
		t1 = mul_modmonom(r->sig,m1);
		t2 = mul_modmonom(g->sig,m2);
		flag = compare_modmonom(t1,t2);
		if(flag != 0){
			NEWSIGSPAIR(sp);
			sp->lcm = lcm;
			sp->i1 = i;
			sp->i2 = n;
			if(flag == 1){	//g_iが主成分
				sp->sig = t1;
				sp->i1 = i;
				sp->i2 = n;
			}else if(flag == -1){	//g_nが主成分
				sp->sig = t2;
				sp->i1 = n;
				sp->i2 = i;
			}
			//CONSNODE(splist,t,sp);
			if(syzygy_criterion(sp) == 0){
				sparray[j] = sp;
				j++;
			}
		}
	}
	*len = j;
	return sparray;
}

Node insert_sigspair_0(Node l,Sigspair s)	//S多項式をsignature順序に沿って挿入及び削除
{
  struct node root;
  Node cur,prev,r;
  Poly p1,p2;
  //Monomial lcm1,lcm2;
  int comp = 1;
  clock_t t0;

  root.next = cur = l;
  prev = &root;
  t0 = clock();
  for ( ; cur != 0; prev = cur, cur = cur->next ){
    comp = compare_modmonom(s->sig,((Sigspair)cur->body)->sig);
    if(comp <= 0){
      break;
    }
  }
  Tinscomp += clock() - t0;
  if(comp != 0){
  	NEWNODE(r); r->body = (void *)s; r->next = cur;
	  prev->next = r;
	}else{
		if(mcomp_simple(s->lcm,((Sigspair)cur->body)->lcm) == -1){
		  cur->body = (void *)s;
		}
	}
  return root.next;
}

void swap(Sigspair *a, Sigspair *b) {
	Sigspair temp = *a;
	*a = *b;
	*b = temp;
}

int partition(Sigspair *sparray, int low, int high) {
	Modmonom pivot = sparray[high]->sig; // 最後の要素をピボットにする
	int i = (low - 1); // 小さい要素のためのインデックス
	for (int j = low; j <= high - 1; j++) {
    // 現在の要素がピボット以下であれば
		if (compare_modmonom(pivot,sparray[j]->sig) >= 0) {
			i++; // インデックスを増やす
			swap(&sparray[i], &sparray[j]); // 要素を交換する
			
		}
	}
	swap(&sparray[i + 1], &sparray[high]); // ピボットを適切な位置に移動
	return (i + 1);
}
void sort_sp(Sigspair *sparray, int low, int high) {
	if (low < high) {
    // パーティションインデックスを取得
		int pi = partition(sparray, low, high);
    // パーティションに基づいて配列をソート
		sort_sp(sparray, low, pi - 1);
		sort_sp(sparray, pi + 1, high);
	}
}

Node insert_sigspair_1(Node l,Sigspair *sparray,int len)	//S多項式をsignature順序に沿って挿入及び削除
{
  struct node root;
  Node cur,prev,r;
  Poly p1,p2;
  Sigspair s;
  //Monomial lcm1,lcm2;
  int i,comp,i1,i2,j1,j2,len1,len2,comp1;
  //comp = 1;
  clock_t t0;

  root.next = cur = l;
  prev = &root;
  for(i = 0; i < len; i++){
	  t0 = clock();
	  s = sparray[i];
	  comp = 1;
	  for ( ; cur != 0; prev = cur, cur = cur->next ){
	    comp = compare_modmonom(s->sig,((Sigspair)cur->body)->sig);
	    if(comp <= 0){
	      break;
	    }
	  }
	  Tinscomp += clock() - t0;
	  if(comp != 0){
			NEWNODE(r); r->body = (void *)s; r->next = cur;
			prev->next = r;
			cur = prev->next;
		}else{
			if(mcomp_simple(s->lcm,((Sigspair)cur->body)->lcm) == -1){
				cur->body = (void *)s;
			}
		}
	}
  return root.next;
}

Node update_sigpairs_0(Node d,int m)	//signature付きspairの更新
{
	int len,i;
	Sigspair *sparray;
	clock_t t0;
	t0 = clock();
	sparray = regular_spair_0(m,&len);
	Tregsp += clock() - t0;
	t0 = clock();
	for(i = 0; i < len; i++){
		d = insert_sigspair_0(d,sparray[i]);
	}
	Tins += clock() - t0;
	return d;
}

clock_t Tsort;

Node update_sigpairs_1(Node d,int m)	//signature付きspairの更新
{
	int len,i;
	Sigspair *sparray;
	clock_t t0;
	t0 = clock();
	sparray = regular_spair_0(m,&len);
	Tregsp += clock() - t0;
	t0 = clock();
	sort_sp(sparray,0,(len-1));
	Tsort += clock() - t0;
	t0 = clock();
	d = insert_sigspair_1(d,sparray,len);
	Tins += clock() - t0;
	return d;
}

Node insert_sigspair_deg(Node l,Sigspair *sparray,int len,int deg,int *fin)	//最小次数のもののみ
{
  struct node root;
  Node cur,prev,r;
  Poly p1,p2;
  Sigspair s;
  //Monomial lcm1,lcm2;
  int i,comp;
  //comp = 1;
  clock_t t0;

  root.next = cur = l;
  prev = &root;
  for(i = 0; i < len; i++){
	  t0 = clock();
	  s = sparray[i];
	  if(s->sig->sch->td != deg){
	  	break;
	  }
	  comp = 1;
	  for ( ; cur != 0; prev = cur, cur = cur->next ){
	    comp = compare_modmonom(s->sig,((Sigspair)cur->body)->sig);
	    if(comp <= 0){
	      break;
	    }
	  }
	  Tinscomp += clock() - t0;
	  if(comp != 0){
	  	NEWNODE(r); r->body = (void *)s; r->next = cur;
		  prev->next = r;
		  cur = prev->next;
		}else{
			if(mcomp_simple(s->lcm,((Sigspair)cur->body)->lcm) == -1){
			  cur->body = (void *)s;
			}
		}
	}
	*fin = i;
	l = root.next;
  return root.next;
}

Node insert_sigspair_2(Node l,Sigspair *sparray,int sta,int len)	//S多項式をsignature順序に沿って挿入及び削除
{
  struct node root;
  Node cur,prev,r;
  Poly p1,p2;
  Sigspair s;
  //Monomial lcm1,lcm2;
  int i,comp;
  //comp = 1;
  clock_t t0;

  root.next = cur = l;
  prev = &root;
  for(i = sta; i < len; i++){
	  t0 = clock();
	  s = sparray[i];
	  comp = 1;
	  for ( ; cur != 0; prev = cur, cur = cur->next ){
	    comp = compare_modmonom(s->sig,((Sigspair)cur->body)->sig);
	    if(comp <= 0){
	      break;
	    }
	  }
	  Tinscomp += clock() - t0;
	  if(comp != 0){
	  	NEWNODE(r); r->body = (void *)s; r->next = cur;
		  prev->next = r;
		  cur = prev->next;
		}else{
			if(mcomp_simple(s->lcm,((Sigspair)cur->body)->lcm) == -1){
			  cur->body = (void *)s;
			}
		}
	}
  return root.next;
  //*l = root.next;
}

Node init_sigpairs_0(){	//signature付きspairの初期設定
	int len,i;
	Node splist;
	len = siggbarray.len;
	splist = 0;
	for(i = 1; i < len; i++){
		splist = update_sigpairs_1(splist,i);
		//printf("check\n");
	}
	return splist;
}

Node f5_0(Node b){
	Node t,d,gblist,splist;
	int i,j;
	//int criS,criM,regred;
	criSY = criMG = regred = 0;
	TcriS = TcriM = Tred = Tadd = Tregsp = Tins = Tinscomp = Tredp = Tsort = 0;
	clock_t t0,t1;
	t1 = clock();
  Sigspair sp;
	init_siggbarray(b);
	init_syzarray(b);
  splist = init_sigpairs_0();
  Sigpoly spoly,r;
  int len,check;
  LONG mins,tm;
  
  tm = 0;
  while(splist != 0){  	
  	sp = (Sigspair)splist->body; splist = splist->next;
	  mins = sp->sig->sch->td;
	  if(mins > tm){
	  	fprintf(stderr,"\n%d:",mins);
	  	tm = mins;
	  }
  	if(syzygy_criterion(sp) == 0){
  		if(mg_criterion(sp) == 0){
  			spoly = sigspoly(sp);
  			t0 = clock();
        r = regular_reduce(spoly,&siggbarray);
  			Tred += clock() - t0;
  			if(r->p != 0){  //Sペアの更新及び中間基底に追加
  				len = siggbarray.len;
  				add_to_siggbarray(r);
  				fprintf(stderr,"(%d)",len);
  				t0 = clock();
          splist = update_sigpairs_1(splist,len);
  				Tadd += clock() - t0;
  			}else{
  				add_to_syzarray(r->sig);
  				fprintf(stderr,".");
  			}
  			regred++;
  		}
  	}
  }
	Sugarp sugp;
	for ( gblist = 0, i = siggbarray.len-1; i >= 0; i-- ) {
		NEWSUGARP(sugp);
		sugp->p = siggbarray.body[i]->p;
		CONSNODE(gblist,t,sugp);
	  //CONSNODE(gblist,t,siggbarray.body[i]);
	}
  t1 = clock() - t1;
  fprintf(stderr,"\n");
  fprintf(stderr,"criS:%d criM:%d regular reduce:%d 0-reduction:%d \n",criSY,criMG,regred,syzarray.len);
	/*fprintf(stderr,"criS=%.3fsec criM=%.3fsec reduce=%.3fsec add=%.3fsec \n",
  	(double)TcriS/(double)CLOCKS_PER_SEC,
    (double)TcriM/(double)CLOCKS_PER_SEC,
    (double)Tred/(double)CLOCKS_PER_SEC,
    (double)Tadd/(double)CLOCKS_PER_SEC);
  fprintf(stderr," reduce : redpoly=%.3fsec \n",
    (double)Tredp/(double)CLOCKS_PER_SEC);
	fprintf(stderr," add : regular sp=%.3fsec insert=%.3fsec \n",
  	(double)Tregsp/(double)CLOCKS_PER_SEC,
    (double)Tins/(double)CLOCKS_PER_SEC);
	fprintf(stderr,"  insert : compare=%.3fsec \n",
  	(double)Tinscomp/(double)CLOCKS_PER_SEC);
  fprintf(stderr,"total=%.3fsec \n",(double)t1/(double)CLOCKS_PER_SEC);*/
  fprintf(stderr,"total SBA=%.3fsec (criS=%.3fsec criM=%.3fsec reduce=%.3fsec update=%.3fsec) \n",
    (double)t1/(double)CLOCKS_PER_SEC,
  	(double)TcriS/(double)CLOCKS_PER_SEC,
    (double)TcriM/(double)CLOCKS_PER_SEC,
    (double)Tred/(double)CLOCKS_PER_SEC,
    (double)Tadd/(double)CLOCKS_PER_SEC);
  return gblist;
}

///////f4///////////////////////

Sigpoly find_reducer(Monomial t,Modmonom smin){	//論文方針2
	Sigpoly g,gmin;
	Modmonom s,msg;
	Monomial m;
	int i;
	s = 0; gmin = 0;
	for(i = 0; i < siggbarray.len; i++){
		g = siggbarray.body[i];
		if(divisible(t,g->p->m) == 1){
			m = div_monomial(t,g->p->m);
			msg = mul_modmonom(g->sig,m);
			if(compare_schreyer(smin,msg) == 1){
				return g;
			}
			if( (s == 0) || (compare_schreyer(s,msg) == 1) ){
				s = msg; gmin = g;
			}
		}
	}
	return gmin;
}

Sigpoly reducer_sig(Monomial m1,Sigpoly p2)
{
  Monomial m;
  Poly p;
  Sigpoly ans; 

  m = div_monomial(m1,p2->p->m);
  NEWPOLY(p); p->c = CurrentRing->one; p->m = m; p->next = 0;
  NEWSIGPOLY(ans);
  ans->p = mul1_poly(p,p2->p);
  ans->sig = mul_modmonom(p2->sig,m);
  return ans;
}

clock_t Tsym1,Tsym2,Tfind,Tsymred,Tsymmerge;

void poly_to_array_sig(Sigspvec *sigv,Sigpoly sigp,Monomial *marray,int len,LONG *tmpval,int *tmppos)
{
  LONG i;
  int t,j;
  j = 0;
  Poly q;
  for ( q = sigp->p; q != 0; q = q->next ) {
    i = find_pos(q->m,marray,len);
    t = i;
    tmppos[j] = t;
    tmpval[j] = q->c.f;
    j++;
  }
  sigv->v.len = j;
  sigv->v.pos = (int *)GC_malloc(j*sizeof(int));
  sigv->v.val = (LONG *)GC_malloc(j*sizeof(LONG));
  for(i = 0; i < j; i++){
  	sigv->v.pos[i] = tmppos[i];
  	sigv->v.val[i] = tmpval[i];
  }
  sigv->sig = sigp->sig;
}

int criterion_T(Poly p,Monomial *marray,int col)
{
	Poly q;
	int i;
	if(p == 0){
		return 1;
	}
	for(i = 0, q = p; i < col; i++){
		if(eq_monomial(q->m,marray[i]) == 1){
			q = q->next;
			if(q == 0){
				return 1;
			}
		}
	}
	return 0;
}

Monomial *merge_marray(Monomial *marray,int col,int *tcol,Node nm)
{
	int i,j,len;
	Monomial *ans;
	len = length(nm) + col;
	ans = (Monomial *)GC_malloc(len*sizeof(Monomial));
	for(i = 0, j = 0; (j < col)&&(nm != 0); i++){
		switch ( mcomp_simple((Monomial)nm->body,marray[j]) ){
			case 0:
				ans[i] = marray[j];
				nm = nm->next;
				j++;
				break;
			case 1:
				ans[i] = (Monomial)nm->body;
				nm = nm->next;
				break;
			case -1:
				ans[i] = marray[j];
				j++;
				break;
		}
	}
	while(nm != 0){
		ans[i] = (Monomial)nm->body;
		i++; nm = nm->next;
	}
	while(j < col){
		ans[i] = marray[j];
		i++; j++;
	}
	*tcol = i;
	return ans;
}

Sigspvec *sort_redmat(Sigspvec *redmat,Sigspvec *tredmat,int nred,int tnred)
{
	int i,n,r1,r2;
	Sigspvec *ans;
	
	n = nred + tnred;
	r1 = r2 = 0;
	ans = (Sigspvec *)GC_malloc(n*sizeof(Sigspvec));
	for(i = 0; i < n; i++){
		if(r1 == nred){
			//i++;
			while(r2 != tnred){
				ans[i] = tredmat[r2];
				r2++; i++;
			}
			break;
		}
		if(r2 == tnred){
			//i++;
			while(r1 != nred){
				ans[i] = redmat[r1];
				r1++; i++;
			}
			break;
		}
		if(redmat[r1].v.pos[0] <= tredmat[r2].v.pos[0]){
			ans[i] = redmat[r1];
			r1++;
		}else{
			ans[i] = tredmat[r2];
			r2++;
		}
	}
	if(i != n){
		fprintf(stderr,"//error//");
	}
	return ans;
}

void poly_to_row(LONG *v,Poly p,Monomial *marray,int len)
{
  LONG i;
  Poly q;

  memset(v,0,len*sizeof(Coef));
  for ( q = p; q != 0; q = q->next ) {
    i = find_pos(q->m,marray,len);
    v[i] = q->c.f;
  }
}

void axpy_f5(LONG *temp,Modmonom sig,Sigspvec spvec){
	LONG head,mod;
	mod = CurrentRing->chr;
	head = temp[spvec.v.pos[0]] % mod;
	if(head == 0){
		return;
	}
	if(compare_schreyer(sig,spvec.sig) != 1){
		return;
	}
	temp[spvec.v.pos[0]] = 0;
	int i;
	for(i = 1; i < spvec.v.len; i++){
		temp[spvec.v.pos[i]] = temp[spvec.v.pos[i]] - head * spvec.v.val[i];
	}
}

Poly row_to_poly(LONG *v,Monomial *marray,int len)
{
  struct poly root;
  int i;
  Coef c;
  Poly p,r;
  Monomial m;

  r = &root;
  for ( i = 0; i < len; i++ ) {
    if ( v[i] != 0 ) {
      m = dup_monomial(marray[i]);
      c.f = v[i];
      APPENDPOLY(r,p,c,m);
    }
  }
  r->next = 0;
  return root.next;
}

Sigpoly regular_reduce_V(Sigpoly s,Sigspvec *redmat,Monomial *marray,int col,int nred)
{
	LONG *v;
	LONG mod;
	int i;
	Sigpoly ans;
	
	mod = CurrentRing->chr;
	v = (LONG *)GC_malloc(col*sizeof(LONG));
	poly_to_row(v,s->p,marray,col);
	for(i = 0; i < nred; i++){
		axpy_f5(v,s->sig,redmat[i]);
	}
	for(i = 0; i < col; i++){
		if(v[i] != 0){
			v[i] = v[i] % mod;
			if(v[i] < 0){
				v[i] += mod;
			}
		}
	}
	NEWSIGPOLY(ans);
	ans->p = row_to_poly(v,marray,col);
	ans->sig = s->sig;
	return ans;
}

int log_gauss(int a,int b)	//[log_b(a)]を返す
{
	int ans,comp;
	ans = 0; comp = b;
	while(a >= comp){
		comp = comp * b;
		ans++;
	}
	return ans;
}

Mononode extension(Mononode m, int d)
{
	Mononode ans;
	NEWMONONODE(ans);
	ans->body = (Node *)GC_realloc(m->body,(m->max + 1)*sizeof(Node));
	ans->max = m->max + 1;
	ans->body[m->max] = 0;
	return ans;
}


Mononode symb_merge_poly_geo(Mononode ans, Poly p, int d, int *power)
{
	int i;
	//Mononode ans = m;
	i = log_gauss(length_poly(p),d);
	while(i >= ans->max){
			ans = extension(ans,d);
	}
	ans->body[i] = symb_merge_poly(ans->body[i],p);
	//printf("0 ");
	while(power[i] < length(ans->body[i])){
		//printf("1 ");
		if(i + 1 == ans->max){
			//m = extension(m,d);
			ans = extension(ans,d);
		}
		//ans->body[i+1] = merge_node_monom(ans->body[i+1],ans->body[i]);
		ans->body[i+1] = merge_mnode(ans->body[i+1],ans->body[i]);
		ans->body[i] = 0;
		i++;
	}
	
	return ans;
}

void symb_merge_poly_geon(Node *m, Poly p, int d, int *power)
{
	int i;
	i = log_gauss(length_poly(p),d);
	m[i] = symb_merge_poly(m[i],p);
}

Monomial top_geo(Mononode m)
{
	Monomial ans;
	Node t;
	int i;
	int (*mcomp)(Monomial,Monomial);
	ans = 0;
	for(i = 0; i < m->max; i++){
		if(m->body[i] != 0){
			//t = m->body[i];
			ans = (Monomial)m->body[i]->body;
			break;
		}
	}
	if(ans == 0){
		//printf("000\n");
		return 0;
	}
	i++;
	while(i < m->max){
		if(m->body[i] != 0){
			//if(mcomp_simple( (Monomial)m->body[i]->body,(Monomial)t->body ) == 1){
			if(mcomp_simple( (Monomial)m->body[i]->body,ans ) == 1){
				//t = m->body[i];
				ans = (Monomial)m->body[i]->body;
			}
		}
		i++;
  }
	//ans = (Monomial)t->body;
  return ans;
}

void print_geo(Mononode m)
{
	Node t;
	int i;
	for(i = 0; i < m->max; i++){
		printf("\n%d ",i);
		for(t = m->body[i]; t != 0; t = t->next){
			print_monomial((Monomial)t->body); printf(" ");
		}
	}
}

void print_geo2(Mononode m)
{
	int i;
	for(i = 0; i < m->max; i++){
		fprintf(stderr,"\n%d:length(%d)",i,length(m->body[i]));
	}
}

void print_geon(Node *m)
{
	Node t;
	int i;
	for(i = 0; i < 10; i++){
		printf("\n%d ",i);
		for(t = m[i]; t != 0; t = t->next){
			print_monomial((Monomial)t->body); printf(" ");
		}
	}
}

Mononode init_geo(int n, int d)
{
	int i,j;
	Mononode gm;
	//fprintf(stderr,"cc0 ");
	NEWMONONODE(gm);
	gm->body = (Node *)GC_malloc(n*sizeof(Node));
	//fprintf(stderr,"cc1 ");
	gm->max = n;
	for( i = 0; i < n; i++){
		gm->body[i] = 0;
	}
	//fprintf(stderr,"cc2 ");
	return gm;
}

void init_power(int d, int *ans)
{
	int i,p,n,m;
	//int *ans;
	n = 2; m = 1;
	for(i = 0; i < 9; i++){
		n *= 10;
	}
	while(n < d){
		n = n/d;
		m++;
	}
	ans = (int *)GC_malloc(m*sizeof(int));
	p = d;
	for(i = 0; i < m; i++){
		ans[i] = p;
		p *= d;
	}
	//return ans;
}

void print_power(int *p)
{
	int i;
	for(i = 0; i < 9; i++){
		fprintf(stderr,"%d ",p[i]);
	}
}

int opt_select_d;
void symbolic_preproc_sig_G(Node sp,Node *splist,Node *redlist,Node *mlist)
{
  struct node redroot,mroot,sproot;
  Node prev,cur,mprev,mcur,m,w,t;
  //Node *dm,*dw;
  Mononode gm,gw;
  Monomial top;
  Sigpoly s,g,red;
  Poly *pa;
  int i,j,len,d,n,im;
  int *power;
  Modmonom smin;
  clock_t t0,t1;
	t0 = clock();
	//fprintf(stderr,"c0 ");
	d = opt_select_d;
	//fprintf(stderr,"c1 ");
	//power = init_power(d);
	//init_power(d,power);
	im = 0; n = 100000000;
	/*while(n > d){
		n = n/d;
		im++;
	}*/
	im = log_gauss(n,d);
	//fprintf(stderr,"c");
	power = (int *)GC_malloc(im*sizeof(int));
	j = d;
	for(i = 0; i < im; i++){
		power[i] = j;
		j *= d;
	}
	//print_power(power);
	//fprintf(stderr,"c2 ");
	gm = init_geo(10,d);
	//fprintf(stderr,"c3 ");
  for ( t = sp; t != 0; t = t->next ) {
    s = sigspoly((Sigspair)t->body);
    //printf(" "); print_poly(s->p);
  	gm = symb_merge_poly_geo(gm,s->p,d,power);
  }
  //fprintf(stderr,"c4 ");
  //print_geo(gm);
  //print_geo2(gm);
  //print_power(power);
  Tsym1 += clock() - t0;
  t0 = clock();
  smin = ((Sigspair)sp->body)->sig;
  gw = gm;
  mprev = &mroot; prev = &redroot;
  
  top = top_geo(gw);
  while(top != 0){
  	//printf(" top111 "); print_monomial(top); printf("\n");
  	APPENDNODE(mprev,mcur,top);
	  t1 = clock();
		g = find_reducer(top,smin);
	  Tfind += clock() - t1;
	  if(g != 0){
	  	t1 = clock();
	  	red = reducer_sig(top,g);
	  	Tsymred += clock() - t1;
	  	APPENDNODE(prev,cur,red);
	  	t1 = clock();
	  	//w = symb_merge_poly(w,red->p);
	  	gw = symb_merge_poly_geo(gw,red->p,d,power);
	  	//symb_merge_poly_geo(gw,red->p,d,power);
	  	Tsymmerge += clock() - t1;
	  }
	  for(i = 0; i < gw->max; i++){
	  	if(gw->body[i] != 0){
				if( eq_monomial( (Monomial)gw->body[i]->body,top) == 1){
					gw->body[i] = gw->body[i]->next;
					//printf("next ");
				}
			}
		}
		top = top_geo(gw);
	}
  prev->next = 0; mprev->next = 0;
  Tsym2 += clock() - t0;
  *redlist = redroot.next; *mlist = mroot.next;
}
///////////////////1224fin//////////////////

clock_t Tsym,Tmake;
Node f5_f4(Node b)
{
	Node t,splist,nd,nd1,gblist,spolylist,redlist,mlist;
	//Node tnd,tnd1,tspolylist,tredlist,tmlist;
	struct node nroot;
	Node prev,cur;
	LONG mins,tm;
	//int i,j,criS,criM,regred,col,len,nred,tcol,tnred;
	int i,j,col,len,nred,tcol,tnred,renew,sta,splen;
	int *tmppos;
	LONG *tmpval;
	Monomial *marray;
	Sigspvec *redmat,*tredmat,*redvec;
	Sigspair sp;
	Sigspair *sparray;
	Sigpoly spoly,r;
	clock_t t0,t1,t2,Tother;
	Modmonom compmod;
	
	criSY = criMG = regred = renew = 0;
	//renew = 0;
	TcriS = TcriM = Tred = Tadd = Tregsp = Tins = Tinscomp = Tredp = Tsym = Tsym1 = Tsym2 = Tfind = Tsymred = Tsymmerge = Tsort = Tmake = 0;
	t1 = clock();
	init_siggbarray(b);
	init_syzarray(b);
  splist = init_sigpairs_0();
  redvec = (Sigspvec *)GC_malloc(1*sizeof(Sigspvec));
  //fprintf(stderr,"c1\n");
  compmod = ((Sigspair)splist->body)->sig;
  while(splist != 0){
  	mins = ((Sigspair)splist->body)->sig->sch->td;
  	fprintf(stderr,"\n%d ",mins);
  	//fprintf(stderr,"c2\n");
  	nd = 0;
  	prev = &nroot;
  	while(splist != 0 && ((Sigspair)splist->body)->sig->sch->td == mins){ //次数毎にSペア集合を作成
  		if(syzygy_criterion((Sigspair)splist->body) == 0){
  			if(mg_criterion((Sigspair)splist->body) == 0){
		  		APPENDNODE(prev,cur,splist->body);
	  		}
	  		//APPENDNODE(prev,cur,splist->body);
	  	}
  		splist = splist->next;
  	}
  	prev->next = 0;
  	nd = nroot.next;
  	if(nd == 0){
  		continue;
  	}
  	spolylist = redlist = mlist = 0;
  	fprintf(stderr,"spoly:%d symbo:",length(nd));
  	t0 = clock();
    symbolic_preproc_sig_G(nd,&spolylist,&redlist,&mlist);  //Simbolic Preprcessing Sig
		t0 = clock() - t0;
	  Tsym += t0;
	  fprintf(stderr,"%.3fsec ",(double)t0/(double)CLOCKS_PER_SEC);
	  //marray作成
	  t0 = clock();
	  col = length(mlist);
	  marray = (Monomial *)GC_malloc(col*sizeof(Monomial));	  
	  //fprintf(stderr,"marray ");
	  for ( i = 0, t = mlist; i < col; i++, t = t->next ){
			marray[i] = (Monomial)t->body;
	  }
	  //fprintf(stderr,"%d)",j);
		//redmat作成
		nred = length(redlist);
		redmat = (Sigspvec *)GC_malloc(nred*sizeof(Sigspvec));
		tmppos = (int *)GC_malloc(col*sizeof(int));
		tmpval = (LONG *)GC_malloc(col*sizeof(LONG));
		for(t = redlist, i = 0; t != 0; i++, t = t->next){  //Redcer集合を疎なベクトルの集合に変換
			poly_to_array_sig(&redmat[i],(Sigpoly)t->body,marray,col,tmpval,tmppos);
		}
		Tmake += clock() - t0;
		fprintf(stderr,"redmat:%dx%d ",nred,col);
		//fprintf(stderr,"c6\n");
		while(nd != 0){
			sp = (Sigspair)nd->body; //nd = nd->next;;
			if(syzygy_criterion(sp) == 0){
				//spoly = sigspoly(sp);
				if(mg_criterion(sp) == 0){
					spoly = sigspoly(sp);
	  	  	if(criterion_T(spoly->p,marray,col) == 0){
	  	  	//単項式リストに含まれない項が生じた場合、reducerと単項式リストを更新
	  	  		fprintf(stderr,"\nrenew ");
	  	  		renew++;
						spolylist = redlist = mlist = 0;
						fprintf(stderr,"spoly:%d symbo:",length(nd));
						t0 = clock();
            symbolic_preproc_sig_G(nd,&spolylist,&redlist,&mlist);
						t0 = clock() - t0;
						Tsym += t0;
						fprintf(stderr,"%.3fsec ",(double)t0/(double)CLOCKS_PER_SEC);
						t0 = clock();
						col = length(mlist);
					  marray = (Monomial *)GC_malloc(col*sizeof(Monomial));
					  for ( i = 0, t = mlist; i < col; i++, t = t->next ){
							marray[i] = (Monomial)t->body;
					  }
						//redmat作成
						nred = length(redlist);
						redmat = (Sigspvec *)GC_malloc(nred*sizeof(Sigspvec));
						tmppos = (int *)GC_malloc(col*sizeof(int));
						tmpval = (LONG *)GC_malloc(col*sizeof(LONG));
						for(t = redlist, i = 0; t != 0; i++, t = t->next){
							poly_to_array_sig(&redmat[i],(Sigpoly)t->body,marray,col,tmpval,tmppos);
						}
						Tmake += clock() - t0;
						fprintf(stderr,"redmat:%dx%d ",nred,col);
	  	  	}
	  	  	t0 = clock();
	  	  	r = regular_reduce_V(spoly,redmat,marray,col,nred);
	  	  	Tred += clock() - t0;
	  	  	regred++;
	  	  	//fprintf(stderr,"c10\n");
	  	  	if(r->p != 0){  //Sペアの更新及び中間基底に追加
	  	  		len = siggbarray.len;
		  	  	//fprintf(stderr,"(%d)",len);
	  	  		//print_poly(r->p);
	  	  		//fprintf(stderr,"\n");
	  				add_to_siggbarray(r);
	  				t0 = clock();
            splist = update_sigpairs_1(splist,len);
	  				Tadd += clock() - t0;
						poly_to_array_sig(&redvec[0],r,marray,col,tmpval,tmppos);
						redmat = sort_redmat(redmat,redvec,nred,1);
						nred++;
		  			t0 = clock();
            t2 = clock();
		  			while(splist != 0 && ((Sigspair)splist->body)->sig->sch->td == mins){
			  			nd = insert_sigspair_0(nd,(Sigspair)splist->body);
							splist = splist->next;
				  	}
				  	Tins += clock() - t2;
		  			Tadd += clock() - t0;
		  			//Tins += clock() - t0;
	  	  	}else{  //syzygyリストに追加
	  	  		add_to_syzarray(r->sig);
	  	  	}
	  	  }
	  	}
	  	nd = nd->next;
		}
		fprintf(stderr,"(%d)",len);
	}
	Sugarp sugp;
	for ( gblist = 0, i = siggbarray.len-1; i >= 0; i-- ) {
		NEWSUGARP(sugp);
		sugp->p = siggbarray.body[i]->p;
		CONSNODE(gblist,t,sugp);
	  //CONSNODE(gblist,t,siggbarray.body[i]);
	}
  t1 = clock() - t1;
  fprintf(stderr,"\n");
  fprintf(stderr,"criS:%d criM:%d regular reduce:%d 0-reduction:%d renew:%d\n",criSY,criMG,regred,syzarray.len,renew);
  fprintf(stderr,"total SBA_F4=%.3fsec (criS=%.3fsec criM=%.3fsec reduce=%.3fsec update=%.3fsec symbo=%.3fsec make=%.3fsec)\n",
    (double)t1/(double)CLOCKS_PER_SEC,
  	(double)TcriS/(double)CLOCKS_PER_SEC,
    (double)TcriM/(double)CLOCKS_PER_SEC,
    (double)Tred/(double)CLOCKS_PER_SEC,
    (double)Tadd/(double)CLOCKS_PER_SEC,
    (double)Tsym/(double)CLOCKS_PER_SEC,
    (double)Tmake/(double)CLOCKS_PER_SEC);
	/*fprintf(stderr,"criS=%.3fsec criM=%.3fsec reduce=%.3fsec update=%.3fsec symbo=%.3fsec make=%.3fsec\n",
  	(double)TcriS/(double)CLOCKS_PER_SEC,
    (double)TcriM/(double)CLOCKS_PER_SEC,
    (double)Tred/(double)CLOCKS_PER_SEC,
    (double)Tadd/(double)CLOCKS_PER_SEC,
    (double)Tsym/(double)CLOCKS_PER_SEC,
    (double)Tmake/(double)CLOCKS_PER_SEC);
	fprintf(stderr," add : regular sp=%.3fsec insert=%.3fsec sort=%.3fsec\n",
  	(double)Tregsp/(double)CLOCKS_PER_SEC,
    (double)Tins/(double)CLOCKS_PER_SEC,
    (double)Tsort/(double)CLOCKS_PER_SEC);
	fprintf(stderr,"  insert : compare=%.3fsec \n",
  	(double)Tinscomp/(double)CLOCKS_PER_SEC);
	fprintf(stderr," symbo : 前半=%.3fsec 後半=%.3fsec\n",
  	(double)Tsym1/(double)CLOCKS_PER_SEC,
    (double)Tsym2/(double)CLOCKS_PER_SEC);
	fprintf(stderr,"  後半 : find=%.3fsec red=%.3fsec merge=%.3fsec\n",
    (double)Tfind/(double)CLOCKS_PER_SEC,
    (double)Tsymred/(double)CLOCKS_PER_SEC,
    (double)Tsymmerge/(double)CLOCKS_PER_SEC);*/
  //fprintf(stderr,"total=%.3fsec \n",(double)t1/(double)CLOCKS_PER_SEC);
  return gblist;
}

int main(int argc,char **argv)
{
  Node vars,out,outm,outr,t;
  int chr,ordid,bpe,alg;
  int opt_printgb,opt_f5;
  
  if ( argc == 2 ) {
    Input = fopen(argv[1],"r"); 
    if ( Input == 0 ) {
      fprintf(stderr,"%s not found\n",argv[1]);
      exit(0);
    }
  } else
    Input = stdin;
  GC_init();
  mp_set_memory_functions(
    (void *(*)(size_t))GC_malloc,
    (void *(*)(void *,size_t,size_t))gc_realloc,
    (void (*)(void *,size_t))GC_free);
  while ( 1 ) {
    yyparse();
    if ( result == 0 ); // ring definition
    else {
      switch ( result->alg ) {
        case ALG_BUCH:
        	//printf("f5_f4:3 f5_0:2 f5:1 buch:0\n");
          printf("f4 style SBA:2 SBA:1 buch:0\n");
        	scanf("%d",&opt_f5);
        	if(opt_f5 >= 1){
        		opt_modorder = 2;
		        opt_select_d = 4;
	        	opt_d1 = 0;
	        	if( CurrentRing->chr == 0 ){
	        		//out = f5_z(result->ideal);
              out = improved_buchbgerger_z(result->ideal);
	        	}else{
	        		if(opt_f5 == 2){
	        			out = f5_f4(result->ideal); //SBA_f4
	        		}else if(opt_f5 == 1){
		        		out = f5_0(result->ideal);  //SBA
		        	}
		        }
        		break;
        	}else{
	          if ( CurrentRing->chr == 0 )
	            out = improved_buchbgerger_z(result->ideal);
	          else
	            out = improved_buchbgerger(result->ideal);
	          break;
	        }
        case ALG_F4:
          out = f4(result->ideal);
          break;
        default:
          out = 0;
          error("not implemented");
          break;
      }
			outm = minimalize(out);
  	  outr = interreduce(outm);
      if ( result->alg == ALG_F4 )
        fprintf(stderr,"symb=%.3fsec rref=%.3fsec add=%.3fsec\n",
          (double)Tsymb/(double)CLOCKS_PER_SEC,
          (double)Trref/(double)CLOCKS_PER_SEC,
          (double)Tadd/(double)CLOCKS_PER_SEC);
      printf("グレブナー基底を表示:1 非表示:0\n");
      scanf("%d",&opt_printgb);
      if(opt_printgb == 1){
      	for ( t = outr; t != 0; t = t->next ) {
        	print_poly(((Sugarp)t->body)->p); printf("\n");
      	}
      }
    }
  }
}

void check()
{
  printf("afo\n");
}
