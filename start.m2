-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")




S = ZZ/101[x,y,z]

I = ideal(x^3,x^2*y,x*y^3,x*y^2*z)
p = principalCone I