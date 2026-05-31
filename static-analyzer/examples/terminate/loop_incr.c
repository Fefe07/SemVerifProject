/*
 * Cours "Sémantique et Application à la Vérification de programmes"
 *
 * Ecole normale supérieure, Paris, France / CNRS / INRIA
 */

void main(){
  int i = 0;
  while (true) i = i + 1;
  assert(i >= 0);
}
