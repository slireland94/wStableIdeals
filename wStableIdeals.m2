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
    "fundRegion",
    "coneWhereShadowsMissQuotient",
    "getLargestLexGeneratorFromList",
    "coneWhereShadowsGenerateIdeal"

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
                branchIndices := for i from maxIndex(leaf) to fm_(leafD) list i;
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
-- feed this B\subseteq Bgens(I)
coneWhereShadowsMissEachotherOld = method();
coneWhereShadowsMissEachotherOld (Ideal,List) := Cone => (I,B) -> (
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
            fbs := factoredIndices(bStart);
            maxTruncbStart := if vDeg < #fbs then ( fbs_vDeg ) else ( maxIndex(bStart) );
            if maxIndex(v) <= maxTruncbStart then (
                print(bStart,v,bEnd);
                ineqs = append(ineqs,getHalfSpace(v,bStart));
                );
            );
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);

-- now i need a function to get the cone where B\subseteq Bgens doesn't collapse
-- feed this B\subseteq Bgens(I)
coneWhereShadowsMissEachother = method();
coneWhereShadowsMissEachother (Ideal,List) := Cone => (I,B) -> (
    S := ring I;
    Bs := for b in sortLex(B) list (sub(b,S));
    n := numgens S;
    r := #Bs;
    ineqs := {};
    tree := treeFromIdeal(I);
    for i from 1 to #Bs-1 do (
        bEnd := Bs_i;
        bStart := getLargestLexGeneratorFromList(bEnd,Bs);
        di := #factoredIndices(bEnd);
        bendPath := for bPath in findPaths(tree,sub(1,S),di) list ( if (last bPath) == bEnd then bPath else continue );
        bendPath = delete(sub(1,S),bendPath_0);
        for v in bendPath do (
            vDeg := #factoredIndices(v);
            fbs := factoredIndices(bStart);
            maxTruncbStart := if vDeg < #fbs then ( fbs_vDeg ) else ( maxIndex(bStart) );
            if maxIndex(v) <= maxTruncbStart then (
                print(bStart,v,bEnd);
                ineqs = append(ineqs,getHalfSpace(v,bStart));
                );
            );
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);


-- feed this B = Bgens(I)
coneWhereShadowsMissQuotient = method();
coneWhereShadowsMissQuotient (Ideal,List) := Cone => (I,B) -> (
    tree := treeFromIdeal(I);
    K := coefficientRing ring I;
    n := numgens ring I;
    gs := gens ring I;
    Slex := K[gs,MonomialOrder=>Lex];
    verts := toList( set (vertices tree) - set (sinks tree) );
    ineqs := {};
    for vert in verts do (
        for b in B do (
            if sub(vert,Slex) > sub(b,Slex) then (
                ineqs = append(ineqs,getHalfSpace(vert,b));
                );
            );
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);


-- finds the lex largest monomial in B which can generate leaf
getLargestLexGeneratorFromList = method();
getLargestLexGeneratorFromList (RingElement,List) := RingElement => (leaf,B) -> (
    S := ring leaf;
    K := coefficientRing S;
    gs := gens S;
    Slex := K[gs,MonomialOrder=>Lex];
    Bs := reverse (for b in sortLex(B) list sub(b,Slex));
    v := sub(leaf,Slex);
    i := 0;
    b := "No Generators Found in List";
    tf := true;
    while i<#Bs and tf do (
        if (Bs_i < v) and isSubset({v},vertices treeFromIdeal(borel monomialIdeal ideal(Bs_i))) then (b := Bs_i; tf=false);
        i = i + 1;
        );
    b);




coneWhereShadowsGenerateIdeal = method();
coneWhereShadowsGenerateIdeal (Ideal,List) := Cone => (I,B) -> (
    gI := (entries gens I)_0;
    S := ring I;
    n := numgens S;
    B2 := for b in B list (sub(b,S));
    C := toList (set gI - set B2);
    ineqs := {};
    for g in C do (
        bg := getLargestLexGeneratorFromList(g,B2);
        ineqs = append(ineqs,getHalfSpace(bg,g));
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);