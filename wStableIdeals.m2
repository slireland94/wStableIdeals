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
    "sortLex",
    "getHalfSpace",
    "coneWhereShadowsMissEachother",
    "coneWhereShadowsMissQuotient",
    "coneWhereShadowsGenerateIdeal",
    "stopMons",
    "treeFromMonomial",
    "stableCone",
    "possibleBgens",
    "stableFan",
    "chamberConeTable",
    "goodWeightCone",
    "goodWeightVector",
    "getLargestLexMonThatGeneratesMon",
    "tableOfTrees",
    "stopDeg",
    "treeFromIdeal",
    "factoredGens"

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
-- CONSTRUCTING TREES
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

treeFromMonomial = method(Options => {stopMons=>{},stopDeg=>null});
treeFromMonomial RingElement := Graph => opts -> m -> (
    S := ring m;
    n := numgens S;
    gs := gens S;
    stops := for mon in opts.stopMons list sub(mon,S);
    fm := factoredIndices(m);
    dm := if opts.stopDeg===null then (#fm) else (opts.stopDeg);
    trunk := for i from 0 to fm_0 list ({sub(1,S),gs_i});
    tree := digraph(trunk);
    tf := true;
    mE := (exponents m)_0;
    newLeafs := for v in (sinks tree) list ( if (not isSubset({v},stops)) and (#factoredIndices(v)<dm) then v else continue );
    while tf do (
        leafs := for v in newLeafs list ( if (not isSubset({v},stops)) and (#factoredIndices(v)<dm) then v else continue );
        if #leafs == 0 then tf = false;
        newLeafs = {};
        for leaf in leafs do (
            leafE := (exponents leaf)_0;
            diffExpVec := for i from 0 to n-1 list ( mE_i - leafE_i );
            maxBranch := n - 1 - position(reverse diffExpVec,i -> i>0);
            minBranch := maxIndex(leaf);
            for i from minBranch to maxBranch do (
                tree = addVertex(tree,leaf*gs_i);
                tree = addEdge(tree,set{leaf*gs_i,leaf});
                newLeafs = append(newLeafs,leaf*gs_i);
                );
            );
        );
    tree);

tableOfTrees = method(Options => {stopMons=>{}});
tableOfTrees List := HashTable => opts -> B -> (
    stops := opts.stopMons;
    L := for b in B list (b => treeFromMonomial(b,stopMons=>stops));
    new HashTable from L);


factoredGens = method();
factoredGens Ideal := Matrix => I -> (
    G := sortLex((entries gens I)_0);
    -- start by making a matrix of factored indices of g\in G
    fG := {};
    fG2 := {};
    longest := 0;
    for g in G do (
        fg := factoredIndices(g);
        gLength := #fg;
        if gLength > longest then longest = gLength;
        fG = append(fG,fg);
        );
    for fg in fG do (
        extra := apply(longest-#fg,i->-1);
        fg2 := join(fg,extra);
        fG2 = append(fG2,fg2);
        );
    fG2);

treeFromIdeal = method();
treeFromIdeal Ideal := Graph => I -> (
    S := ring I;
    n := numgens S;
    gs := gens S;
    G := factoredGens(I);
    k := #(G_0);
    branches := {};
    for m in G do (
        branches = append(branches,{sub(1,S),gs_(m_0)});
        for i from 0 to k-2 do (
            if m_(i+1) >= 0 then (
                prev := product(for j from 0 to i list gs_(m_j));
                branches = append(branches,{prev,prev*gs_(m_(i+1))});
                );
            );
        );
    tree := digraph(toList set branches);
    tree);

--------------------------------------------------------
--------------------------------------------------------
-- CONVEX GEOMETRY
--------------------------------------------------------
--------------------------------------------------------


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

