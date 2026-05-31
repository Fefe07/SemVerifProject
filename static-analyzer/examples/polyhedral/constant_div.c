/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 */

void main(){
  int i = 9;
  int j = -2;
  int x = i / j; // We follow towards zero convention
  assert(x == -4);

  int a = 44;
  int b = 4;
  int r = a / b; // We follow towards zero convention
  assert(r == 11);
}
