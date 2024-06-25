-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")
needsPackage("Graphs")

n = 4;
maxW = 5;
minD = 3;
maxD = 5;
K = ZZ/101;
S = K[x_1..x_n];

--w = rsort(for i from 0 to n-1 list (random(1,maxW)));
--m1 = randomMonomial(random(minD,maxD),S);
--m2 = randomMonomial(random(minD,maxD),S);
--m3 = randomMonomial(random(minD,maxD),S);
--I = borelClosure(ideal(m1,m2,m3));

--G = getBgensTrees(I)

--L = delete(1, flatten (for g in G list leaves g_1))
--J = sub(ideal(L),S)

--print(I==J)

--B = borelGens(I)
--v = ((entries gens I)_0)_0
--b = getLargestLexMonSmallerThanMon(B,v)

--S = ZZ/101[x,y,z]
--I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
--I = ideal(x^5,x^4*y*z,x^4*y^2,x^4*z^3,x^3*y^2*z^2,x^3*y^3*z,x^3*y^4,x^3*z^5,x^3*y*z^4)
--bgens = borelGens(I)
--gI = (entries gens I)_0


--B = {z^5,y*z^2,y^2}
--comp = toList (set gI - set B)

--c1 = getConeWhereBgensMissesQuotient(I)
--c2 = getConeWhereListGeneratesList(B,comp)
--stableCone = intersection(c1,c2)

--c3 = getConeWhereListMissesItself(B)

---c = intersection({c1,c3})

--Bgens = {z^5,y*z^2,x*z,y^2}
--B = {z^5,y*z^2}
--C = toList ( set Bgens - set B )
--c1 = getConeWhereListGeneratesList(B,C)
--c2 = getConeWhereListMissesItself(B)
--c = intersection(c1,c2)
--print(rays c)

S = ZZ/101[x,y]
I = ideal(x^4,x^3*y^2,x^2*y^4,x*y^7,y^9)
bgens = borelGens(I)


B = bgens 
--B = {y^9,x^2*y^4}
C = toList (set bgens - set B)
c1 = getConeWhereBgensMissesQuotient(I)
c2 = getConeWhereListGeneratesList(B,C)
c3 = getConeWhereListMissesItself(B)
c = intersection({c1,c2,c3})