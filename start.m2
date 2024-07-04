-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]
--I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
--I = borelClosure(ideal(x*z^2,x*y^3*z^2,z^6))

I = ideal(x^2,x*y^4,y^5,x*y^3*z^3,x*y^2*z^4,x*y*z^5)

I = borelClosure(ideal(x*y*z^7),Degrees=>{7,5,1})

T = treeFromIdeal(I)
p = principalCone(I)