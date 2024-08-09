-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")




S = ZZ/101[x_1..x_3]



I = borelClosure(ideal(x_1*x_2*x_3^2),Weights=>{3,2,1})