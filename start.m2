-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

a = {0,0,5}
w = {4,3,1}


n = #a;
K = ZZ/101;
S = K[x,y,z,Degrees=>w];

u = vectorToMonomial(vector a, S)

J = ideal(u)
--I = borel monomialIdeal(u);
I = borelClosure(J,Degrees=>w);


Gu = shadowGraph(u)
