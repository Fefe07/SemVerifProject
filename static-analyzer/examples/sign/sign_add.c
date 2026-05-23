/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 */

void main(){
  int i = 10;
  int j = -2;
  int x = i + j;
  assert(x == 8); //@KO

  int a = 0;
  int b = 0;
  int y = a + b;
  assert(y == 0);

  int c = 2;
  int d = 2;
  int z = 2 - 2;
  assert(z <= 0); //@KO
}
