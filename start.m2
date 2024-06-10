-- this is so i don't have to type everything every time


needsPackage("wStableIdeals",Reload=>true)

K = ZZ/101;
S = K[x,y,z];
I = borelClosure(ideal(z^5),Degrees=>{4,3,1});
