/*
 * Ici, le domaine des congruences permet de montrer que i est impair en fin de boucle, 
 * le domaine des intervalles montre que i est dans [10,11]
 * on a donc que i = 11 grace à la réduction
 */

void main() {

    int i = 1 ;

    while(i<10){
        i += 2 ;
    }
    assert(i == 11) ;

}