-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]
m = x*y^2*z
m = randomMonomial(random ZZ,S)
if m == sub(1,S) then m = randomMonomial(random ZZ,S)

w = {9,3,2}
T = treeFromMonomial(m,Weights=>w)
J = ideal(sinks T)
I = borelClosure(ideal(m),Degrees=>w)
print(m,I==J)


tI = treeFromIdeal(I)