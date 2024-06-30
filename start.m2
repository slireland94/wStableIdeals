-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]
--I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
I = borelClosure(ideal(x*z^2,x*y^3*z^2,z^6))


F = stableFan I
