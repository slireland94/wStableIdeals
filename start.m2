-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")




S = ZZ/101[x,y]


G = {y^7,x*y^4,x^2*y^3,x^3*y,x^4}
w = {3,2}
I = borelClosure(ideal(G),Weights=>w)
p = principalWeightVector I
