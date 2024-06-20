-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

n = 5;
maxW = 5;
maxD = 7;
K = ZZ/101;
S = K[x_1..x_n];
w = rsort(for i from 0 to n-1 list (random(1,maxW)));
m = randomMonomial(random(1,maxD),S);

print(m,w)

elapsedTime(G = shadowGraph2(m,Degrees=>w);
L = delete(1,leaves G);
J = sub(ideal(L),S));
elapsedTime(I = borelClosure(ideal(m),Degrees=>w));

print(I==J)

vs = getLeafEqns(G,m)


--gstop = shadowGraph2(u,Degrees=>w,stopMons=>{x_1*x_2})
--lstop = delete(1,leaves gstop)
--jstop = sub(ideal(lstop),S)
