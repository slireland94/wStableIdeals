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
    "coneWhereShadowsGenerateIdeal",
    "stopMons",
    "treeFromMonomial",
    "tableOfTrees",
    "getLargestLexMonThatGeneratesMon"

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


treeFromMonomialOld = method(Options => {stopMons=>{}});
treeFromMonomialOld RingElement := Graph => opts -> m -> (
    S := ring m;
    gs := gens S;
    stops := for mon in opts.stopMons list sub(mon,S);
    fm := factoredIndices(m);
    trunk := for i from 0 to fm_0 list ({sub(1,S),gs_i});
    tree := digraph(trunk);
    tf := true;
    i := #fm-1;
    while tf do (
        leafs := for v in (sinks tree) list ( if (not isSubset({v},stops)) then v else continue );
        for leaf in leafs do (
            leafD := #factoredIndices(leaf);
            minBranch := maxIndex(leaf);
            maxBranch := if leafD < #fm then ( fm_leafD ) else ( max(fm) );
            branchIndices := for i from minBranch to maxBranch list i;
            newVerts := for i in branchIndices list leaf*gs_i;
            newEdges := for i in branchIndices list set {leaf*gs_i,leaf};
            tree = addVertices(tree,newVerts);
            tree = addEdges'(tree,newEdges);
            );
        i = i - 1;
        if #leafs == 0 or i == 0 then tf = false;
        );
    tree);


treeFromMonomial = method(Options => {stopMons=>{}});
treeFromMonomial RingElement := Graph => opts -> m -> (
    S := ring m;
    gs := gens S;
    stops := for mon in opts.stopMons list sub(mon,S);
    fm := factoredIndices(m);
    trunk := for i from 0 to fm_0 list ({sub(1,S),gs_i});
    tree := digraph(trunk);
    tf := true;
    i := #fm-1;
    while tf do (
        leafs := for v in (sinks tree) list ( if (not isSubset({v},stops)) then v else continue );
        for leaf in leafs do (
            leafD := #factoredIndices(leaf);
            minBranch := maxIndex(leaf);
            maxBranch := if leafD < #fm then ( fm_leafD ) else ( max(fm) );
            branchIndices := for i from minBranch to maxBranch list i;
            newVerts := for i in branchIndices list leaf*gs_i;
            newEdges := for i in branchIndices list set {leaf*gs_i,leaf};
            tree = addVertices(tree,newVerts);
            tree = addEdges'(tree,newEdges);
            );
        i = i - 1;
        if #leafs == 0 or i == 0 then tf = false;
        );
    tree);

tableOfTrees = method(Options => {stopMons=>{}});
tableOfTrees List := HashTable => opts -> B -> (
    stops := opts.stopMons;
    L := for b in B list (b => treeFromMonomial(b,stopMons=>stops));
    new HashTable from L);




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

-- gets the largest lex monomial from the list B that generates v
getLargestLexMonThatGeneratesMon = method();
getLargestLexMonThatGeneratesMon (List,RingElement) := RingElement => (B,v) -> (
    S := ring v;
    gs := gens S;
    K := coefficientRing S;
    Slex := K[gs,MonomialOrder=>Lex];
    Bs := for b in sort B list sub(b,Slex);
    vlex := sub(v,Slex);
    r := #Bs;
    tf := true;
    TT := tableOfTrees(Bs,stopMons=>{vlex});
    answer := "No monomials in list generate given monomial!";
    for i from 0 to r-1 do (
        b := Bs_i;
        if tf and b <= vlex and isSubset({vlex},sinks TT#(b)) then (
            answer = sub(b,S);
            tf = false;
            );
        );
    answer);


coneWhereShadowsMissQuotient = method();
coneWhereShadowsMissQuotient Ideal := Cone => I -> (
    n := numgens ring I;
    bgens := borelGens(I);
    G := (entries gens I)_0;
    TT := tableOfTrees(bgens,stopMons=>G);
    ineqs := {};
    for b in bgens do (
        tb := TT#b;
        notIdeal := toList(set vertices tb - set sinks tb);
        for u in notIdeal do (
            ineqs = append(ineqs,getHalfSpace(u,b));
            );
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);

coneWhereShadowsMissEachother = method();
coneWhereShadowsMissEachother List := Cone => B -> (
    n := numgens ring B_0;
    ineqs := {};
    for b in B do (
        mb := getLargestLexMonThatGeneratesMon(delete(b,B),b);
        if class mb === String then (continue) else (
            ineqs = append(ineqs,getHalfSpace(b,mb));
            );
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);

coneWhereShadowsGenerateIdeal = method();
coneWhereShadowsGenerateIdeal (List,Ideal) := Cone => (B,I) -> (
    n := numgens ring I;
    ineqs := {};
    G := toList (set (entries gens I)_0 - set B);
    print(G);
    for v in G do (
        mv := getLargestLexMonThatGeneratesMon(B,v);
        ineqs = append(ineqs,getHalfSpace(mv,v));
        print(mv,v);
        );
    returnCone := if ineqs == {} then fundRegion(n) else intersection(coneFromHData(matrix ineqs),fundRegion(n));
    returnCone);