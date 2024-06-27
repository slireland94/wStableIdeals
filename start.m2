-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]
I = borelClosure(ideal(z^7),Degrees=>{7,6,1})
I = borelClosure(ideal(y^2*z^5,y^3*z,x^2*z))

B = {y^2*z^5,y^3*z}

c1 = coneWhereShadowsMissEachother(B)
c2 = coneWhereShadowsMissQuotient(I)
c3 = coneWhereShadowsGenerateIdeal(B,I)
c = intersection({c1,c2,c3})
print(B,rays c)