-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

a = {7,0,0,2,1}
w = {5,4,3,2,1}


n = #a;
K = ZZ/101;
S = K[x_1..x_5];

u = vectorToMonomial(vector a, S)
I = borelClosure(ideal(u));
G = shadowGraph2(u)
