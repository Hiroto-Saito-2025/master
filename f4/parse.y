%{
#define malloc(x) GC_malloc(x)
#define free(x) GC_free(x)

#include <ctype.h>
#include <sys/types.h>
#include <sys/stat.h>
#include "gb.h"
void yyerror(char *);
Indata result;
int ringdef = 0;

void afo() {
  printf("afo\n");
}
%}

%start start

%union {
  Poly f;
  Node n;
  Indata d;
  char *s;
  int i;
  pointer p;
}

%token <s> VAR STR
%token <s> INT
%token <i> BUCH F4 RING
%token <i> '+' '-' '*' '/' '^' '[' ']'

%type <f> expr
%type <n> node vnode
%type <d> stat

%right '=' ASS
%left '+' '-' 
%left PLUS
%left MINUS
%left '*' '/'
%right '^'

%%

/*
start : node ';'
  { 
    result = $1; 
    YYACCEPT; 
  }
;
*/
start :  stat 
  { result = $1; YYACCEPT; }
;
stat : ';'
  { $$ = 0; }
     | RING {ringdef=1;} '(' '[' vnode ']' ',' INT ',' INT ',' INT ')' {ringdef = 0; } ';'
  {  
    CurrentRing = create_ring($5,atoi($8),atoi($10),atoi($12)); 
    $$ = 0;
  }
     | BUCH '(' node ')' ';'
  {  Indata d; NEWINDATA(d); d->alg = ALG_BUCH; d->ideal = $3; $$=d; }
     | F4 '(' node ')' ';'
  {  Indata d; NEWINDATA(d); d->alg = ALG_F4; d->ideal = $3; $$=d; }
;
vnode : STR
  { $$ = append_to_node(0,$1); }
     | vnode ',' STR
  { $$ = append_to_node($1,$3); }
node : expr
  { $$ = append_to_node(0,$1); }
     | node ',' expr
  { $$ = append_to_node($1,$3); }
expr : '+' expr   %prec PLUS
  { $$ = $2; }
     | '-' expr   %prec MINUS
  { $$ = neg_poly($2); }
     | expr '+' expr
  { $$ = add_poly($1,$3); }
     | expr '-' expr
  { $$ = sub_poly($1,$3); }
     | expr '*' expr
  { $$ = mul_poly($1,$3); }
     | expr '/' expr
  { $$ = divc_poly($1,$3); }
     | expr '^' INT
  { $$ = power_poly($1,$3); }
     | INT
  { $$ = itop($1); }
     | VAR
  { $$ = vtop($1); }
     | '(' expr ')'
  { $$ = $2; }
;
%%

void yyerror(char *s)
{
  fprintf(stderr,"parser : %s\n",s);
}

int yylex()
{
  int c,i,bufsize;
  char *buf,*s;;

  buf = GC_malloc(BUFSIZ);
  bufsize = BUFSIZ;

  switch ( c = skipspace() ) {
    case EOF :  
     exit(0);
      break;
    case '+': case '-': case '*': case '/': case '^':
    case '(': case ')': case ';': case ',': case '[': case ']':
     yylval.i = c;
     return c;
     break;
    default:
     break;
  }
  if ( isdigit(c) ) {
    buf[0] = c;
    for ( i = 1; ; i++ ) {
      if ( i == bufsize ) {
        bufsize *= 2;
        buf = GC_realloc(buf,bufsize);
      }
      c = getc(Input);
      if ( !isdigit(c) ) {
        ungetc(c,Input);
        buf[i] = 0;
        break;
      } else
        buf[i] = c;
    }
    s = (char *)GC_malloc(i+1);
    strcpy(s,buf);
    yylval.s = s;
    return INT;
  } else if ( isalpha(c) ) {
    buf[0] = c;
    for ( i = 1; ; i++ ) {
      c = getc(Input);
      if ( !isalnum(c) ) {
        ungetc(c,Input);
        buf[i] = 0;
        break;
      } else
        buf[i] = c;
    }
    if ( !strcmp(buf,"ring") ) return RING;
    if ( !strcmp(buf,"buch") ) return BUCH;
    if ( !strcmp(buf,"f4") ) return F4;
    s = GC_malloc(i+1);
    strcpy(s,buf);
    yylval.s = s;
    if ( ringdef == 1 )
      return STR;
    else
      return VAR;
  } else
   return 0; // dummy return
}
