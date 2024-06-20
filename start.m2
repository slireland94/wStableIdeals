-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

n = 5;
maxW = 6;
maxD = 9;
K = ZZ/101;
S = K[x_1..x_n];
w = rsort(for i from 0 to n-1 list (random(1,maxW)));





u = randomMonomial(random(1,maxD),S)
I = borelClosure(ideal(u),Degrees=>w);
print("borelClosure done")
G = shadowGraph2(u,Degrees=>w)
print("shadowGraph2 done")
L = delete(1,leaves G);
J = sub(ideal(L),S)
print(u,w,I==J)


gstop = shadowGraph2(u,Degrees=>w,stopMons=>{x_1*x_2})
lstop = delete(1,leaves gstop)
jstop = sub(ideal(lstop),S)
