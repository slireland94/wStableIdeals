-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)


S = ZZ/101[x,y,z]
I = borelClosure(ideal(z^5),Degrees=>{4,3,1})
T = treeFromIdeal(I)

