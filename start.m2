-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")




S = ZZ/101[x,y,z]


m = x*y*z^2
w = {1,1,1}


I = borelClosure(ideal(m),Weights=>w)
B = borelGens(I,Weights=>w)
P = principalCone(I)

C = catalanDiagram(m,Weights=>w)
P = poincareSeries(m,Weights=>w)
betti I

