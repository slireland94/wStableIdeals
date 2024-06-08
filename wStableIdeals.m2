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
    "wBorelClosure",
    }

--  path = append(path, ".Macaulay2/GitHub/wStableIdeals/")


--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING W-STABLE IDEALS
--------------------------------------------------------
--------------------------------------------------------

psiMap = method();

psiMap = (S,degs) -> (
    L := {};
    n := numgens S;
    K := coefficientRing S;
    R := K[local y_1..local y_n];
    ys := gens R;
    for i from 1 to n do (
        L = append(L,y_i^(degs_(i-1)));
        );
    psi := map(R,S,L)
    );


wBorelClosure = method();

wBorelClosure = (I,w) -> (
    S := ring I;
    startIdeal := monomialIdeal I;
    psi := psiMap(S,w);
    psI := monomialIdeal psi(startIdeal);
    psIbar := borel psI;
    Ibar := preimage_psi(psIbar)
    );



