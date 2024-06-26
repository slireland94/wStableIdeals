-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)


S = ZZ/101[x,y,z]
I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
T = treeFromIdeal(I)


B = borelGens(I)
B = {z^5,y*z^2}
c = coneWhereShadowsMissEachother(I,B)
c2 = coneWhereShadowsMissQuotient(I,borelGens(I))