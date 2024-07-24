newPackage(
    "wStableIdeals",
    Version => "1.1",
    Date => "July 2024",
    Headline => "Computations for w-Stable Ideals",
    Authors => {{   Name => "Seth Ireland",
                    Email => "seth.ireland@colostate.edu", 
                    HomePage => "sethireland.com"   }},
    AuxiliaryFiles => false,
    DebuggingMode => false,
    PackageExports => {"Graphs","Polyhedra","SRdeformations"},
    Keywords => {"Combinatorial Commutative Algebra"}
    )

export {
    "borelClosure",
    "borelGens",
    "iswStable",
    "treeFromMonomial",
    "catalanDiagram",
    "poincareSeries",
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
    w := if opts.Weights === null 
        then (for i from 1 to n list 1) else opts.Weights;
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
    w := if opts.Weights===null 
        then apply(n,i->1) else opts.Weights;
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
    Bgens := for b in bgens list 
        ((gens (preimage_psi(ideal(b))))_0)_0;
    if not iswStable(J,w) then (
        print(toString(J) | " is not " | toString(w) | "-stable.");
        Bgens = null;
        );
    Bgens);


--------------------------------------------------------
--------------------------------------------------------
-- CATALAN DIAGRAMS
--------------------------------------------------------
--------------------------------------------------------

catalanDiagram = method(Options => {Weights=>null});
catalanDiagram RingElement := Matrix => opts -> m -> (
    S := ring m;
    K := coefficientRing S;
    n := numgens S;
    R := K[vars(1..n)];
    w := if opts.Weights===null 
        then apply(n,i->1) else opts.Weights;
    psi := psiMap(S,R,w);
    M := psi(m);
    fM := factoredIndices(M);
    weirdfM := join(fM,apply(w_0-1,i->n-1));
    d := #fM;
    C := mutableMatrix(ZZ,#weirdfM+1,n);
    C_(0,0) = 1;
    for i from 1 to numrows(C)-1 do (
        for j from 0 to weirdfM_(i-1) do (
            if (0<=i-w_j and i-w_j<d) then (
                if weirdfM_(i-w_j) >= j then (
                    rowAbove := for k from 0 to j 
                        list C_(i-w_j,k);
                    C_(i,j) = sum(rowAbove);
                    );
                );
            );
        );
    matrix C);


poincareSeries = method(Options => {Weights=>null});
poincareSeries RingElement := RingElement => opts -> m -> (
    n := numgens ring m;
    w := if opts.Weights===null 
        then apply(n,i->1) else opts.Weights;
    C := catalanDiagram(m,Weights=>w);
    runningSum := {};
    rng := ZZ[vars(19..20)];
    t := (gens rng)_0;
    u := (gens rng)_1;
    n := #w;
    d := numRows C - w_0;
    for a from d to d+w_0-1 do (
        for b from 1 to n do (
            thing := C_(a,b-1)*u*t^a*product(for k from 1 to b-1 list (1+u*t^(w_(k-1))));
            runningSum = append(runningSum,thing);
            );
        );
    sum(runningSum));


--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING TREES
--------------------------------------------------------
--------------------------------------------------------

maxIndex = method();
maxIndex RingElement := ZZ => (m) -> (
    expVec := (exponents m)_0;
    maxNonzero := position(expVec,i->i!=0,Reverse=>true);
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
treeFromMonomial RingElement := Digraph => opts -> m -> (
    S := ring m;
    K := coefficientRing S;
    n := numgens S;
    w := if opts.Weights===null 
        then apply(n,i->1) else (opts.Weights);
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
        leafs := for v in (sinks tree) list 
            (if #factoredIndices(psi(v))<d then v else continue);
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
treeFromIdeal Ideal := Digraph => I -> (
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
                someList := for j from 0 to i list gs_(m_j);
                prev := product(someList);
                next := prev*gs_(m_(i+1));
                branches = append(branches,{prev,next});
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

-- gets space where branching structure of T_{w,m} matches at v
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
        );
    -- make sure sinks have degree greater than or equal to m
    for v in sink do (
        ineqs = append(ineqs,sigmaUV(m,v));
        );
    f := fundRegion(n);
    hdata := matrix ineqs;
    returnCone := intersection(f,coneFromHData(hdata));
    returnCone);

principalWeightVector = method();
principalWeightVector Ideal := List => I -> (
    c := principalCone I;
    n := numgens ring I;
    r := rays c;
    A := (transpose matrix {apply(n,i->0)}) | r;
    p := convexHull A;
    i := 2;
    tf := true;
    returnPt := null;
    if dim c < n then (tf = false; print(toString I | " is not principally w-stable."));
    while tf do (
        B := A*i;
        i = i+1;
        p = convexHull B;
        tf = (interiorLatticePoints p == {});
        if tf == false then returnPt = (interiorLatticePoints p)_0;
        );
    returnPt);


--------------------------------------------------------
--------------------------------------------------------
-- DOCUMENTATION
--------------------------------------------------------
--------------------------------------------------------

beginDocumentation()

doc ///
  Key
    wStableIdeals
  Headline
    Basic computations with w-stable ideals
  Description
    Text
      {\bf Overview:}
      
      w-stable ideals are a generalization of strongly stable ideals.
      
      {\bf References:}
      
      [FMS11] C.A. Francisco, J. Mermin, J. Schweig: Borel generators, {\it Journal of Algebra}, 332(1), 522-542, 2011.
      @BR{}@ Available at @HREF{"https://arxiv.org/abs/1006.1436"}@.
      

      
      {\bf Key user functions:}

        {\it Weighted Borel Generators:}

          @TO borelClosure@ -- Compute the Borel closure of a monomial ideal

          @TO iswStable@ -- Test whether a monomial ideal is w-stable with respect to a given weight vector

          @TO borelGens@ -- Compute the Borel generators of a strongly stable ideal

        {\it Principal w-Stable Ideals:}

          @TO treeFromMonomial@ -- Compute the tree associated with a principal w-stable ideal
          
          @TO catalanDiagram@ -- Compute the Catalan diagram associated with a principal w-stable ideal
 
          @TO poincareSeries@ -- Compute the Poincare series of a principal w-stable ideal

          @TO principalCone@ -- Compute the principal cone of a strongly stable ideal 

          @TO principalWeightVector@ -- Compute a weight vector for which a strongly stable ideal is principally w-stable  
///   


doc ///
  Key
    borelClosure
  Headline
    Compute the Borel closure of a monomial ideal
  Usage
    borelClosure I
  Inputs
    I : Ideal
  Outputs
    : Ideal
  Description
   Text
      Returns the Borel closure of the input ideal
      
   Example
     ZZ/101[x,y,z];
     borelClosure(ideal(x*y*z))
///

doc ///
  Key
    Weights
    [borelClosure,Weights]
  Headline
    Option to set the weight vector for the Borel closure
  Description
   Text
    This option can be used to specify the weight vector when taking a Borel closure
    
    The default is the vector of ones (corresponding to the classic Borel closure)
    
   Example
     ZZ/101[x,y,z];
     borelClosure(ideal(x*y*z),Weights=>{3,2,1})
///


doc ///
  Key
    iswStable
  Headline
    Test whether an ideal is w-stable for a given weight vector
  Usage
    iswStable(I,w)
  Inputs
    I : Ideal
    w : List
  Outputs
    : Boolean
  Description
   Text
      Returns Boolean value of whether I is w-stable
      
   Example
     ZZ/101[x,y];
     iswStable(ideal(y^4,x*y^2,x^2),{2,1})

   Example
     ZZ/101[x,y];
     iswStable(ideal(y^4,x*y^2,x^2),{3,1})
///


doc ///
  Key
    borelGens
  Headline
    Compute the Borel generators of a strongly stable ideal
  Usage
    borelGens I
  Inputs
    I : Ideal
  Outputs
    : List
  Description
   Text
      Returns the Borel generators of a strongly stable ideal
      
   Example
     ZZ/101[x,y];
     borelGens ideal(y^4,x*y^2,x^2)
///

doc ///
  Key
    Weights
    [borelGens,Weights]
  Headline
    Option to set the weight vector for computing weighted Borel generators
  Description
   Text
    This option can be used to specify the weight vector when computing Borel generators
    
    The default is the vector of ones (corresponding to the classic Borel generators)

    Given a weight vector for which the ideal is not w-stable, returns null
    
   Example
     ZZ/101[x,y];
     borelGens(ideal(y^4,x*y^2,x^2),Weights=>{2,1})

   Example
     ZZ/101[x,y];
     borelGens(ideal(y^4,x*y^2,x^2),Weights=>{3,1})
///


doc ///
  Key
    treeFromMonomial
  Headline
    Compute the n-ary tree associated with a given monomial
  Usage
    treeFromMonomial m
  Inputs
    m : RingElement
  Outputs
    : Digraph
  Description
   Text
      Computes the n-ary tree corresponding to m
      
   Example
     ZZ/101[x,y];
     treeFromMonomial x*y^3

   Example
     ZZ/101[x,y,z];
     treeFromMonomial y^2*z
///

doc ///
  Key
    Weights
    [treeFromMonomial,Weights]
  Headline
    Option to set the weight vector for treeFromMonomial
  Description
   Text
    This option can be used to specify the weight vector when n-ary trees associated with monomials
    
    The default is the vector of ones (corresponding to the classic Borel generators)

   Example
     ZZ/101[x,y];
     treeFromMonomial(x*y^3,Weights=>{3,1})
     
   Example
     ZZ/101[x,y,z];
     treeFromMonomial(y^2*z,Weights=>{4,2,1})
///


doc ///
  Key
    catalanDiagram
  Headline
    Compute the Catalan diagram associated with a given monomial
  Usage
    catalanDiagram m
  Inputs
    m : RingElement
  Outputs
    : Matrix
  Description
   Text
      Computes the Catalan diagram corresponding to a given monomial
      
   Example
     ZZ/101[x,y];
     catalanDiagram x*y^3

   Example
     ZZ/101[x,y,z];
     catalanDiagram y^2*z
///

doc ///
  Key
    Weights
    [catalanDiagram,Weights]
  Headline
    Option to set the weight vector for treeFromMonomial
  Description
   Text
    This option can be used to specify the weight vector when computing Catalan diagrams
    
    The default is the vector of ones (corresponding to the classic Catalan diagrams)

   Example
     ZZ/101[x,y];
     catalanDiagram(x*y^3,Weights=>{3,1})
     
   Example
     ZZ/101[x,y,z];
     catalanDiagram(y^2*z,Weights=>{4,2,1})
///


doc ///
  Key
    poincareSeries
  Headline
    Compute the Poincare series associated with a given monomial
  Usage
    catalanDiagram m
  Inputs
    m : RingElement
  Outputs
    : RingElement
  Description
   Text
      Computes the Poincare series of the principal strongly stable ideal generated by m
      
   Example
     ZZ/101[x,y];
     poincareSeries x*y^3

   Example
     ZZ/101[x,y,z];
     poincareSeries y^2*z
///

doc ///
  Key
    Weights
    [poincareSeries,Weights]
  Headline
    Option to set the weight vector for poincareSeries
  Description
   Text
    This option can be used to specify the weight vector when computing Poincare series
    
    The default is the vector of ones (corresponding to the standard grading)

   Example
     ZZ/101[x,y];
     poincareSeries(x*y^3,Weights=>{3,1})
     
   Example
     ZZ/101[x,y,z];
     poincareSeries(y^2*z,Weights=>{4,2,1})
///


doc ///
  Key
    principalCone
  Headline
    Compute the principal cone of a given strongly stable ideal
  Usage
    principalCone I
  Inputs
    I : Ideal
  Outputs
    : Cone
  Description
   Text
      Computes the principal cone of I

   Example
     ZZ/101[x,y];
     principalCone(ideal(y^4,x*y^2,x^2))
      
   Example
     ZZ/101[x,y,z];
     principalCone(ideal(x^3,x^2*y,x*y^3,x*y^2*z))
///


doc ///
  Key
    principalWeightVector
  Headline
    Compute a principal weight vector
  Usage
    principalCone I
  Inputs
    I : Ideal
  Outputs
    : Cone
  Description
   Text
      Computes a weight vector for which a given strongly stable ideal is principally w-stable (if one exists)

      This method gets a weight vector from the interior of the principal cone

   Example
     ZZ/101[x,y];
     principalWeightVector ideal(y^4,x*y^2,x^2)
      
   Example
     ZZ/101[x,y,z];
     principalWeightVector ideal(x^3,x^2*y,x*y^3,x*y^2*z)
///


--------------------------------------------------------
--------------------------------------------------------
-- TESTS AND END
--------------------------------------------------------
--------------------------------------------------------


TEST ///
        S = ZZ/101[x,y,z];
        G = {z^5};
        w = {4,3,1};
        I = borelClosure(ideal(G),Weights=>w);
        assert ( borelGens(I,Weights=>w) == G )
///

end

restart
installPackage "wStableIdeals"
check "wStableIdeals"