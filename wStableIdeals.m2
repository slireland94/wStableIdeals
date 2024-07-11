newPackage(
    "wStableIdeals",
    Version => "0.1",
    Date => "July 25, 2024",
    Headline => "A Package for Computing with w-Stable Ideals",
    Authors => {{ Name => "Seth Ireland", Email => "seth.ireland@colostate.edu", HomePage => "sethireland.com"}},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageExports => {"Graphs","Polyhedra","SRdeformations"}
    )

export {
    "borelClosure",
    "iswStable",
    "borelGens",
    "treeFromMonomial",
    "principalCone",
    "principalWeightVector",
    }


--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING W-STABLE IDEALS AND BASIC COMPUTATIONS
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


borelClosure = method(Options => {Weights => null});
borelClosure Ideal := Ideal => opts -> I -> (
    S := ring I;
    n := numgens S;
    w := if opts.Weights === null then for i from 1 to n list 1 else opts.Weights;
    startIdeal := monomialIdeal I;
    K := coefficientRing S;
    R := K[vars (1..n)];
    psi := psiMap(S,R,w);
    psI := monomialIdeal psi(startIdeal);
    psIbar := borel psI;
    Ibar := preimage_psi(psIbar)
    );


iswStable = method();
iswStable (Ideal,List) := Boolean => (I,w) -> (
    Ibar := borelClosure(I,Weights=>w);
    I==Ibar);

hatShift = method();
hatShift RingElement := RingElement => mon -> (
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

borelGens = method(Options => {Weights => null});
borelGens Ideal := List => opts -> J -> (
    S := ring J;
    K := coefficientRing S;
    n := numgens S;
    R := K[vars(1..n)];
    w := if opts.Weights===null then apply(n,i->1) else opts.Weights;
    psi := psiMap(S,R,w);
    I := psi(J);
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
    Bgens := for b in bgens list ((gens (preimage_psi(ideal(b))))_0)_0;
    Bgens);


 



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

treeFromMonomial = method(Options => {Weights=>null});
treeFromMonomial RingElement := Graph => opts -> m -> (
    S := ring m;
    K := coefficientRing S;
    n := numgens S;
    w := if opts.Weights===null then apply(n,i->1) else (opts.Weights);
    R := K[vars(1..n)];
    psi := psiMap(S,R,w);
    psim := psi(m);
    fm := factoredIndices(psim);
    d := #fm;
    gs := gens S;
    trunk := for i from 0 to fm_0 list ({sub(1,S),gs_i});
    tree := digraph(trunk);
    tf := true;
    while tf do (
        leafs := for v in (sinks tree) list ( if #factoredIndices(psi(v)) < d  then v else continue );
        if #leafs == 0 then tf = false;
        newLeafs := {};
        for leaf in leafs do (
            fleaf := factoredIndices(psi(leaf));
            maxBranch := fm_(#fleaf);
            minBranch := maxIndex(leaf);
            for i from minBranch to maxBranch do (
                newVert := leaf*gs_i;
                tree = addVertex(tree,newVert);
                tree = addEdge(tree,set{newVert,leaf});
                newLeafs = append(newLeafs,newVert);
                );
            );
        leafs = newLeafs;
        );
    tree);




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

-- gets space where degree of v is larger or equal to degree of u
sigmaUV = method();
sigmaUV (RingElement,RingElement) := List => (u,v) -> (
    a := (exponents u)_0;
    b := (exponents v)_0;
    ineq := for i from 0 to #a-1 list ( b_i - a_i );
    ineq);

-- gets space where branching structure of T_{w,m} agrees (k=max(trunc_{degv+1}(\psi(m))))
tauMV = method();
tauMV (RingElement,RingElement,ZZ) := List => (m,v,k) -> (
    a := (exponents m)_0;
    b := (exponents v)_0;
    ineq1 := for i from 0 to k-2 list ( b_i - a_i );
    ineq2 := for i from k-1 to #a-1 list ( b_i );
    ineq := join(ineq1,ineq2);
    ineq);

principalCone = method();
principalCone Ideal := Cone => I -> (
    m := (sortLex((entries gens I)_0))_0;
    S := ring I;
    n := numgens S;
    gs := gens S;
    tree := treeFromIdeal(I);
    verts := vertices(tree);
    sink := sinks(tree);
    branchPoints := toList( set verts - set sink );
    ineqs := {};
    -- make sure every branch is correct
    for v in branchPoints do (
        k := 1;
        for j from 0 to n-1 do (
            if isSubset({v*gs_j},verts) then k = j+1;
            );
        ineqs = append(ineqs,tauMV(m,v,k));
        ineqs = append(ineqs,-1*tauMV(m,v,k+1));
        print(m,v,k);
        print(ineqs);
        );
    -- make sure sinks have degree greater than or equal to m
    for v in sink do (
        ineqs = append(ineqs,sigmaUV(m,v));
        );
    returnCone := intersection(fundRegion(n),coneFromHData(matrix ineqs));
    returnCone);

principalWeightVector = method();
principalWeightVector Ideal := List => I -> (
    c := principalCone I;
    n := numgens ring I;
    r := rays c;
    A := (transpose matrix {apply(n,i->0)}) | r;
    p := convexHull A;
    i := 2;
    while interiorLatticePoints p == {} do (
        B := A*i;
        i = i+1;
        p = convexHull B;
        );
    (interiorLatticePoints p)_0);