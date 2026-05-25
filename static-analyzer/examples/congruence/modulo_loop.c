
void main() {

    int i = 0 ;
    int x = 0 ;
    int j = rand(0,10);
    while(i<10){
        x += j ;
    }
    assert(x % j == 0) ;

}