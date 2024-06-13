newPackage(
    "wStableIdeals",
    Version => "0.1",
    Date => "June 30, 2024",
    Headline => "A Package for Computing with w-Stable Ideals",
    Authors => {{ Name => "Seth Ireland", Email => "seth.ireland@colostate.edu", HomePage => "sethireland.com"}},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"Polyhedra","SRdeformations"}
    )

export {
    "psiMap",
    "borelClosure",
    "socleGens",
    "hatShift",
    "borelGens",
    "halfPlanes",
    "fundRegion",
    "goodCones",
    "stableRegion"
    
    }

--  path = append(path, ".Macaulay2/GitHub/wStableIdeals/")


--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING W-STABLE IDEALS
--------------------------------------------------------
--------------------------------------------------------


psiMap = method();
psiMap := (S,R,degs) -> (
    L := {};
    n := numgens S;
    ys := gens R;
    for i from 0 to n-1 do (
        L = append(L,ys_i^(degs_i));
        );
    psi := map(R,S,L)
    );


borelClosure = method(Options => {Degrees => null});
borelClosure Ideal := Ideal => opts -> I -> (
    S := ring I;
    n := numgens S;
    w := if opts.Degrees === null then for i from 1 to n list 1 else opts.Degrees;
    startIdeal := monomialIdeal I;
    K := coefficientRing S;
    R := K[vars (1..n)];
    print(S,R,w);
    psi := psiMap(S,R,w);
    psI := monomialIdeal psi(startIdeal);
    psIbar := borel psI;
    Ibar := preimage_psi(psIbar)
    );


--------------------------------------------------------
--------------------------------------------------------
-- FINDING GOOD WEIGHT VECTORS
--------------------------------------------------------
--------------------------------------------------------

socleGens = method();
socleGens Ideal := List => I -> (
    m := ideal gens ring I;
    soc := (entries gens quotient(I,m))_0
    );

hatShift = method();
hatShift = mon -> (
    expVec := (exponents mon)_0;
    n := #expVec;
    hatExpVec := {};
    count := 0;
    for i from 0 to n-1 do (
        count = count + expVec_i;
        hatExpVec = append(hatExpVec,count);
        );
    monHat := vectorToMonomial(vector hatExpVec,ring mon)
    );

borelGens = method();
borelGens Ideal := List => I -> (
    G := (entries gens I)_0;
    Ghat := {};
    for g in G do (
        Ghat = append(Ghat,hatShift(g));
        );
    Ihat := ideal(Ghat);
    bgensHat := set (entries mingens Ihat)_0;
    bgens := {};
    for u in G do (
        uHat := hatShift(u);
        if bgensHat#?uHat then bgens = append(bgens,u);
        );
    bgens);


--INPUT: u,v: monomials
--OUTPUT: cone of weight vectors for which u "w-generates" v
halfPlanes = method();
halfPlanes = (u,v) -> (
    a := (exponents u)_0;
    b := (exponents v)_0;
    n := #a;
    finalIneqs := {};
    for j from 1 to n do (
        jIneqs := {};
        for i from 1 to j do (
            jIneqs = append(jIneqs,b_(i-1)-a_(i-1));
            );
        for i from j+1 to n do (
            jIneqs = append(jIneqs,0);
            );
        finalIneqs = append(finalIneqs,jIneqs);
        );
    finalIneqs);

-- possible weights region (nonincreasing)
fundRegion = n -> (
    Rays := {};
    for i from 0 to n-1 do (
        iRay := {};
        for j from 0 to i do (
            iRay = append(iRay,1);
            );
        for j from i+1 to n-1 do (
            iRay = append(iRay,0);
            );
        Rays = append(Rays,iRay);
        );
    coneFromVData(transpose(matrix Rays)));

-- collection of cones where u does not generate v
goodCones = (u,v) -> (
    gC := {};
    n := numgens ring u;
    fund := fundRegion(n);
    badC := coneFromHData (matrix halfPlanes(u,v));
    hs := halfspaces badC;
    for i from 0 to (numgens target hs - 1) do (
        t := intersection(coneFromHData (hs^{i}*-1),fund);
        gC = append(gC,t);
        );
    gC);


-- stable region
stableRegion = (I) -> (
    bgens := borelGens(I);
    sgens := socleGens(I);
    PCs := {};
    n := numgens ring I;
    g := gens ring I;
    K := coefficientRing ring I;
    tempRing := K[g,MonomialOrder=>Lex];
    fund := fundRegion(n);
    for b in bgens do (
        for s in sgens do (
            if s%I != 0 and b>s then (
                PCs = append(PCs,goodCones(b,s));
                );
            );
        );
    Fs := for p in PCs list posHull rays fan p;
    stblR := intersection(Fs)
    );


