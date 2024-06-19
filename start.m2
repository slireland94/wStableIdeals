-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")




a = {1,2,1}
w = {3,2,2}


n = #a;
K = ZZ/101;
S = K[x_1..x_n,Degrees=>w];

u = vectorToMonomial(vector a, S)

J = ideal(u)
--I = borel monomialIdeal(u);
I = borelClosure(J,Degrees=>{3,2,2});
