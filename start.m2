-- this is so i don't have to type everything every time


needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

K = ZZ/101;
S = K[x,y,z];
d = {2,3,3}
J = randomMonomialIdeal(d,S)
J = ideal(z^5)
I = borelClosure(J,Degrees=>{4,3,1});
P = stableRegion(I)
print rays P