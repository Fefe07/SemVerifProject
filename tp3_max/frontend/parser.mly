(*
  Cours "Sémantique et Application à la Vérification de programmes"
  
  Charles de Haro 2025
  Ecole normale supérieure, Paris, France / CNRS / INRIA
*)


(*
  Parser for a very simple C-like "curly bracket" language.
  
  There should be exactly one shift/reduce conflict, due to nested 
  if-then-else constructs. The resolution picked by menhir should be correct.
 *)

%{
open AbstractSyntax
%}

/* tokens */
/**********/

%token TOK_TRUE
%token TOK_FALSE
%token TOK_WHILE
%token TOK_IF
%token TOK_ELSE
%token TOK_HALT
%token TOK_RAND
%token TOK_ASSERT
%token TOK_PRINT

%token TOK_LPAREN
%token TOK_RPAREN
%token TOK_LCURLY
%token TOK_RCURLY
%token TOK_STAR
%token TOK_PLUS
%token TOK_MINUS
%token TOK_EXCLAIM
%token TOK_DIVIDE
%token TOK_PERCENT
%token TOK_LESS
%token TOK_GREATER
%token TOK_LESS_EQUAL
%token TOK_GREATER_EQUAL
%token TOK_EQUAL_EQUAL
%token TOK_NOT_EQUAL
%token TOK_AND_AND
%token TOK_BAR_BAR
%token TOK_SEMICOLON
%token TOK_COMMA
%token TOK_EQUAL

%token <string> TOK_id
%token <string> TOK_int

%token TOK_EOF

/* priorities of binary operators (lowest to highest) */
%left TOK_BAR_BAR
%left TOK_AND_AND
%left TOK_EQUAL_EQUAL TOK_NOT_EQUAL
%left TOK_LESS TOK_GREATER TOK_LESS_EQUAL TOK_GREATER_EQUAL
%left TOK_PLUS TOK_MINUS
%left TOK_STAR TOK_DIVIDE TOK_PERCENT


/* entry-points */
/****************/

%start<AbstractSyntax.toplevel list AbstractSyntax.ext> file

%%

/* toplevel */
/************/

file: t=ext(list(toplevel)) TOK_EOF { t }

toplevel:
| d=ext(stat)           { Tstmt d }

id:
| e=TOK_id { Id e }

/* expressions */
/***************/

const:
| e=TOK_int { Eint (Z.of_string e) }
| TOK_TRUE  { Ebool true }
| TOK_FALSE { Ebool false }

primary_expr:
| TOK_LPAREN e=expr TOK_RPAREN     { e }
| e=ext(id)                        { Eid e }
| e=ext(const)                     { Econst e }
| TOK_RAND TOK_LPAREN e1=ext(sign_int_literal)  
           TOK_COMMA  e2=ext(sign_int_literal) TOK_RPAREN
  { let z1, e1 = e1 in
    let z2, e2 = e2 in
    Erand ((Z.of_string z1, e1), (Z.of_string z2, e2)) }


/* integer with optional sign */
sign_int_literal:
| i=TOK_int            { i }
| TOK_PLUS i=TOK_int   { i }
| TOK_MINUS i=TOK_int  { "-"^i }


unary_expr:
| e=primary_expr                   { e }
| o=unary_op e=ext(unary_expr)     { Eunop (o, e) }

%inline unary_op:
| TOK_PLUS           { Eplus }
| TOK_MINUS          { Eminus }
| TOK_EXCLAIM        { Enot }


binary_expr:
| e=unary_expr                                        { e }
| e=ext(binary_expr) o=binary_op f=ext(binary_expr)   { Ebinop (o, e, f) }

%inline binary_op:
| TOK_STAR           { Emultiply }
| TOK_DIVIDE         { Edivide }
| TOK_PERCENT        { Emodulo }
| TOK_PLUS           { Eadd }
| TOK_MINUS          { Esub }
| TOK_LESS           { Elt }
| TOK_GREATER        { Egt }
| TOK_LESS_EQUAL     { Ele }
| TOK_GREATER_EQUAL  { Ege }
| TOK_EQUAL_EQUAL    { Eequal }
| TOK_NOT_EQUAL      { Enequal }
| TOK_AND_AND        { Eand }
| TOK_BAR_BAR        { Eor }

expr:
| e=binary_expr { e }

lvalue:
| i=TOK_id   { Var (Id i) }


/* statements */
/**************/

block:
| TOK_LCURLY l=list(ext(stat)) TOK_RCURLY  { l }

stat:
| l=block                     
  { Sblock l }

| e=ext(lvalue) TOK_EQUAL f=ext(expr) TOK_SEMICOLON
  { Sassign (e, f) }

| TOK_IF TOK_LPAREN e=ext(expr) TOK_RPAREN s=ext(stat)
  { Sif (e, s, None) }

| TOK_IF TOK_LPAREN e=ext(expr) TOK_RPAREN s=ext(stat) TOK_ELSE t=ext(stat) 
  { Sif (e, s, Some t) }

| TOK_WHILE TOK_LPAREN e=ext(expr) TOK_RPAREN s=ext(stat)
  { Swhile (e, s) }

| TOK_ASSERT TOK_LPAREN e=ext(expr) TOK_RPAREN TOK_SEMICOLON
  { Sassert e }

| TOK_PRINT TOK_LPAREN l=separated_list(TOK_COMMA,ext(lvalue)) TOK_RPAREN TOK_SEMICOLON
  { Sprint l }

| TOK_HALT TOK_SEMICOLON
  { Shalt }


/* utilities */
/*************/

/* adds extent information to rule */
%inline ext(X): 
| x=X { x, ($startpos, $endpos) }


%%
