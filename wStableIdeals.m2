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
    "borelClosure",
    "borelGens",
    "treeFromIdeal",
    "maxIndex",
    "factoredIndices",
    "sortLex",
    "coneWhereShadowsMissEachother",
    "getHalfSpace",
    "fundRegion"

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
-- COMPUTING BOREL GENERATORS
--------------------------------------------------------
--------------------------------------------------------




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




--------------------------------------------------------
--------------------------------------------------------
-- FINDING GOOD WEIGHT VECTORS
--------------------------------------------------------
--------------------------------------------------------


maxIndex = method();
maxIndex RingElement := ZZ => (m) -> (
    expVec := (exponents m)_0;
    maxNonzero := position(expVec, i -> i!=0 ,Reverse=>true);
    maxNonzero);


factoredIndices = method();
factoredIndices RingElement := List => m -> (
    expVec := (exponents m)_0;
    factorList := {};
    n := #expVec;
    for i from 0 to n-1 do (
        for j from 0 to expVec_i-1 do (
            factorList = append(factorList,i);
        );
    );
    factorList);


sortLex = method();
sortLex List := List => (A) -> (
    S := ring A_0;
    K := coefficientRing S;
    gs := gens S;
    S2 := K[gs,MonomialOrder=>Lex];
    A2 := for a in A list ( sub(a,S2) );
    A3 := sort A2;
    A4 := for a in A3 list ( sub(a,S) );
    A4);


-- construct the tree corresponding to a strongly stable ideal
-- vertices are monomials
-- leaves are G(I)
-- edges are weighted by the w_i

treeFromIdeal = method();
treeFromIdeal Ideal := Graph => J -> (
    if not isMonomialIdeal J then print("Ideal is Not a Monomial Ideal!") else I:= monomialIdeal J;
    if not isBorel I then print("Ideal is Not Strongly Stable!") else (
        bgens := sortLex(borelGens(I));
        gI := (entries gens I)_0;
        m := bgens_0;
        S := ring m;
        gs := gens S;
        fm := factoredIndices(m);
        trunk := for i from 0 to fm_0 list ({sub(1,S),gs_i});
        tree := digraph(trunk);
        tf := true;
        while tf do (
            leafs := for v in (sinks tree) list ( if not isSubset({v},gI) then v else continue );
            for leaf in leafs do (
                leafD := #factoredIndices(leaf);
                branchIndices := for i from maxIndex(leaf) to fm_(leafD-1) list i;
                newVerts := for i in branchIndices list leaf*gs_i;
                newEdges := for i in branchIndices list set {leaf*gs_i,leaf};
                tree = addVertices(tree,newVerts);
                tree = addEdges'(tree,newEdges);
                );
            if #leafs == 0 then tf = false;
            );
        );
    tree);


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



-- gets space where u generates v
getHalfSpace = method();
getHalfSpace (RingElement,RingElement) := Cone => (u,v) -> (
    a := (exponents u)_0;
    b := (exponents v)_0;
    ineq := for i from 0 to #a-1 list ( b_i - a_i );
    ineq);


-- now i need a function to get the cone where B\subseteq Bgens doesn't collapse
coneWhereShadowsMissEachother = method();
coneWhereShadowsMissEachother (Ideal,List) := Cone => (I,B) -> (
    S := ring I;
    Bs := for b in sortLex(B) list (sub(b,S));
    n := numgens S;
    r := #Bs;
    ineqs := {};
    tree := treeFromIdeal(I);
    for i from 0 to r-2 do (
        bStart := Bs_(i);
        bEnd := Bs_(i+1);
        di := #factoredIndices(bEnd);
        bendPath := for bPath in findPaths(tree,sub(1,S),di) list ( if (last bPath) == bEnd then bPath else continue );
        bendPath = delete(sub(1,S),bendPath_0);
        for v in bendPath do (
            vDeg := #factoredIndices(v);
            maxTruncbStart := (factoredIndices(bStart))_(vDeg-1);
            print(maxTruncbStart);
            if maxIndex(v) <= maxTruncbStart then (
                print(bStart," does not generate ",v,getHalfSpace(v,bStart));
                ineqs = append(ineqs,getHalfSpace(v,bStart));
                );
            );
        );
    intersection(coneFromHData(matrix ineqs),fundRegion(n)));

