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
m1 = randomMonomial(random(1,maxD),S);
m2 = randomMonomial(random(1,maxD),S);
m3 = randomMonomial(random(1,maxD),S);
I = borelClosure(ideal(m1,m2,m3));

G = getBgensTrees(I)

L = delete(1, flatten (for g in G list leaves g))
J = sub(ideal(L),S)

print(I==J)


