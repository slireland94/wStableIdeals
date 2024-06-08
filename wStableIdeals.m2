newPackage(
    "wStableIdeals",
    Version => "0.1",
    Date => "June 30, 2024",
    Headline => "A Package for Computing with w-Stable Ideals",
    Authors => {{ Name => "Seth Ireland", Email => "seth.ireland@colostate.edu", HomePage => "sethireland.com"}},
    AuxiliaryFiles => false,
    DebuggingMode => true,
    PackageImports => {"Polyhedra"}
    )

export {
    "psiMap",
    "borelClosure",
    }

--  path = append(path, ".Macaulay2/GitHub/wStableIdeals/")


--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING W-STABLE IDEALS
--------------------------------------------------------
--------------------------------------------------------


--getWSFromDim = method(Options => {Degrees => null})

--getWSFromDim ZZ := List => opts -> d -> (


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


s = 7;

--wBorelClosure = (I,w) -> (
  --  S := ring I;
    ---startIdeal := monomialIdeal I;
    --psi := psiMap(S,w);
    --psI := monomialIdeal psi(startIdeal);
    --psIbar := borel psI;
    --Ibar := preimage_psi(psIbar)
    --);
