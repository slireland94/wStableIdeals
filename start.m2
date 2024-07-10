-- this is so i don't have to type everything every time


-- path = append(path, ".Macaulay2/GitHub/wStableIdeals/")

needsPackage("wStableIdeals",Reload=>true)
needsPackage("RandomIdeals")

S = ZZ/101[x,y,z]

--m = x*y^2*z
--m = randomMonomial(random ZZ,S)
--if m == sub(1,S) then m = randomMonomial(random ZZ,S)

m = z^5
w = {4,3,1}
I = borelClosure(ideal(m),Degrees=>w)
C = principalCone I
