-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)


S = ZZ/101[x,y,z]
I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
T = treeFromIdeal(I)


B = {z^5}
c1 = coneWhereShadowsMissEachother(I,B)
c2 = coneWhereShadowsMissQuotient(I,borelGens(I))
c3 = coneWhereShadowsGenerateIdeal(I,B)
c = intersection({c1,c2,c3})
print(rays c)