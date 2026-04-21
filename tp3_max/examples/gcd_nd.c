a = rand(5,15);
b = rand(3,8);

if (a < 0) a = -a;
if (b < 0) b = -b;
while (b > 0) {  // try changing this to b >= 0
  tmp = b;
  b = a % b;
  a = tmp;
 }
assert (b==0); // should be true
//assert (a>6); // try uncommenting this line
tmp = 0;  
print (a);

