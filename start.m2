-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

n = 4;
maxW = 5;
minD = 3;
maxD = 5;
K = ZZ/101;
S = K[x_1..x_n];
w = rsort(for i from 0 to n-1 list (random(1,maxW)));
m1 = randomMonomial(random(minD,maxD),S);
m2 = randomMonomial(random(minD,maxD),S);
m3 = randomMonomial(random(minD,maxD),S);
I = borelClosure(ideal(m1,m2,m3));

G = getBgensTrees(I)

L = delete(1, flatten (for g in G list leaves g_1))
J = sub(ideal(L),S)

print(I==J)

B = borelGens(I)
v = ((entries gens I)_0)_0
b = getLargestLexMonSmallerThanMon(B,v)



S = K[x,y]
I = ideal(y^4,x*y^2,x^2)
Bgens = {y^4,x*y^2,x^2}
B = {y^4}
C = {x^2,x*y^2}
c = getConeWhereListGeneratesList(B,C)


