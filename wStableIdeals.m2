newPackage(
    "wStableIdeals",
    Version => "0.1",
    Date => "June 30, 2024",
    Headline => "A Package for Computing with w-Stable Ideals",
    Authors => {{ Name => "Seth Ireland", Email => "seth.ireland@colostate.edu", HomePage => "sethireland.com"}},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"Polyhedra","SRdeformations","Graphs"}
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
    "stableRegion",
    "shadowGraph",
    "maxIndex",
    "factoredIndices",
    "stopIdeal",
    "shadowGraph2",
    "stopMons",
    "getBgensTrees",
    "getLargestLexMonSmallerThanMon",
    "getConeWhereListGeneratesList",
    "getHalfSpace"
    
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


--------------------------------------------------------
--------------------------------------------------------
-- N-ARY TREES
--------------------------------------------------------
--------------------------------------------------------

maxIndex = method();
maxIndex RingElement := ZZ => (m) -> (
    expVec := (exponents m)_0;
    maxNonzero := position(expVec, i -> i!=0 ,Reverse=>true);
    maxNonzero);


factoredIndices = method();
factoredIndices (RingElement,List) := List => (m,w) -> (
    expVec := (exponents m)_0;
    factorList := {};
    n := #expVec;
    for i from 0 to n-1 do (
        for j from 0 to expVec_i-1 do (
            for k from 0 to w_i-1 do (
                factorList = append(factorList,i);
                );
            );
        );
    factorList);


-- Input: m from a PolynomialRing
-- Optional: Degrees=>w (weight vector); stopIdeal=>I (will stop branching when leaves are in I)
-- Output: G_w(m)
shadowGraph2 = method(Options => {Degrees=>null,stopMons=>{}});
shadowGraph2 RingElement := Graph => opts -> m -> (

    S := ring m;
    K := coefficientRing S;
    n := numgens S;
    g1 := gens S;

    w := if opts.Degrees === null then for i from 1 to n list 1 else opts.Degrees;
    Sw := K[g1,Degrees=>w];
    gs := gens Sw;
    u := sub(m,Sw);
    ufactored := factoredIndices(u,w);
    d := (degree u)_0;

    G := graph(for i from 0 to min(ufactored) list ({1,gs_i}));
    --G := graph({{1,gs_0}});
    L := delete(1, leaves G);
    stops := for stopMon in opts.stopMons list sub(stopMon,Sw);
    buds := for l in L list (if ( (degree l)_0 < d ) and ( not isSubset({l},stops) ) then l else continue);
    while #buds > 0 do (
        for bud in buds do (
            budFactored := factoredIndices(bud,w);
            budDeg := #budFactored;
            budMax := max(budFactored);
            upperBound := if budDeg < #ufactored then (ufactored_budDeg) else (max(ufactored));
            for j from budMax to upperBound do (
                G = addVertex(G,bud*gs_j);
                G = addEdge(G,set {bud,bud*gs_j});
                );
            );            
        L = delete(1, leaves G);
        buds = for l in L list (if ( (degree l)_0 < d ) and ( not isSubset({l},stops) ) then l else continue);
        );

    G);




-- Edit: shadowGraph2 labelled vertices with mons from wrong ring...subbed things back into S
-- Input: m from a PolynomialRing
-- Optional: Degrees=>w (weight vector); stopIdeal=>I (will stop branching when leaves are in I)
-- Output: G_w(m)
shadowGraph3 = method(Options => {Degrees=>null,stopMons=>{}});
shadowGraph3 RingElement := Graph => opts -> m -> (

    S := ring m;
    K := coefficientRing S;
    n := numgens S;
    g1 := gens S;

    w := if opts.Degrees === null then for i from 1 to n list 1 else opts.Degrees;
    Sw := K[g1,Degrees=>w];
    gs := gens Sw;
    u := sub(m,Sw);
    ufactored := factoredIndices(u,w);
    d := (degree u)_0;

    G := graph(for i from 0 to min(ufactored) list ({1,g1_i}));
    --G := graph({{1,gs_0}});
    L := delete(1, leaves G);
    stops := for stopMon in opts.stopMons list sub(stopMon,Sw);
    buds := for l in L list (if ( (degree l)_0 < d ) and ( not isSubset({l},stops) ) then l else continue);
    while #buds > 0 do (
        for bud in buds do (
            budFactored := factoredIndices(bud,w);
            budDeg := #budFactored;
            budMax := max(budFactored);
            upperBound := if budDeg < #ufactored then (ufactored_budDeg) else (max(ufactored));
            for j from budMax to upperBound do (
                G = addVertex(G,sub(bud*g1_j,S));
                G = addEdge(G,set {sub(bud,S),sub(bud*g1_j,S)});
                );
            );            
        L = delete(1, leaves G);
        buds = for l in L list (if ( (degree l)_0 < d ) and ( not isSubset({l},stops) ) then l else continue);
        );

    G);



-- method to get all the subleaves from a graph
getBgensTrees = method();
getBgensTrees Ideal := List => (I) -> (
    GI := (entries gens I)_0;
    Bgens := borelGens(I);
    print(Bgens,GI);
    bTrees := for mi in Bgens list ( {mi,shadowGraph3(mi,stopMons=>GI)} );
    bTrees);


getLargestLexMonSmallerThanMon = method();
getLargestLexMonSmallerThanMon (List,RingElement) := RingElement => (B,v) -> (
    S := ring v;
    K := coefficientRing S;
    gs := gens S;
    S2 := K[gs,MonomialOrder=>Lex];
    B2 := for b in B list ( sub(b,S2) );
    sortedB := sort B2;
    s := #sortedB;
    v2 := sub(v,S2);
    r := max( for i from 0 to s-1 list ( if sortedB_i <= v2 then i else continue ));
    largestLexBgen := sub(sortedB_r,S);
    largestLexBgen);


-- gets space where u generates v
getHalfSpace = method();
getHalfSpace (RingElement,RingElement) := Cone => (u,v) -> (
    a := (exponents u)_0;
    b := (exponents v)_0;
    ineq := for i from 0 to #a-1 list ( b_i - a_i );
    ineq);

-- generates the cone where a list of monomials B generates a list of monomials C
getConeWhereListGeneratesList = method();
getConeWhereListGeneratesList (List,List) := Cone => (B,C) -> (
    vCones := {};
    n := numgens ring B_0;
    for v in C do (
        mr := getLargestLexMonSmallerThanMon(B,v);
        sigmaRv := getHalfSpace(mr,v);
        vCones = append(vCones,sigmaRv);
        print(mr,v,sigmaRv)
        );
    capSigma := intersection(fundRegion(n),coneFromHData(matrix vCones));
    capSigma);