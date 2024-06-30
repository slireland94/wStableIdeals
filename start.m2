-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]
--I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
--I = borelClosure(ideal(x*z^2,x*y^3*z^2,z^6))

I = ideal(x^2,x*y^2,y^4,x*y*z^3,y^3*z^5)

--B = borelGens(I)
--B = {y^3*z^5,y^4,x*y*z^3}
--c0 = coneWhereShadowsMissQuotient(I)
--c1 = coneWhereShadowsGenerateIdeal(B,I)
--c2 = coneWhereShadowsMissEachother(B)

--c = intersection({c0,c1,c2})

F = stableFan I
