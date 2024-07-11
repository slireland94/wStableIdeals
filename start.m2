-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]
n = numgens S


m = x*y^2*z



w = {5,3,1}

I = borelClosure(ideal(m),Weights=>w)
B = borelGens(I,Weights=>w)

P = principalCone(I)