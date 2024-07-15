-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")




S = ZZ/101[x,y]


m = y^4
w = {2,1}
I = borelClosure(ideal(m),Weights=>w)
print("ideal computed")
B = borelGens(I,Weights=>{3,1})


--B = borelGens(I,Weights=>w)
--P = principalCone(I)
--print("cone computed")

--C = catalanDiagram(m,Weights=>w)
--P = poincareSeries(m,Weights=>w)
--betti I

