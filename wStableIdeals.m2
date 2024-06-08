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


--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING W-STABLE IDEALS
--------------------------------------------------------
--------------------------------------------------------


psiMap = (S,degs) -> (
    L := {};
    n := numgens S;
    K := coefficientRing S;
    R := K[y_1..y_n];
    for i from 1 to n do (
    L := append(L,y_i^(degs_(i-1)));
    );
    psi := map(R,S,L)
    );

wBorelClosure = (I,w) -> (
    S := ring I;
    startIdeal := monomialIdeal I;
    psi := psiMap(S,w);
    psI := monomialIdeal psi(startIdeal);
    psIbar := borel psI;
    Ibar := preimage_psi(psIbar)
    );



/// Example: The weight vector of all ones gives the classic Borel Closure
--K = ZZ/101;
--w = {1,1,1};
--n = #w;
--S = K[x_1..x_n,Degrees=>w];
--Bgensw = {x_1*x_2*x_3^2};
--Ibar = wBorelClosure(ideal(Bgensw),w)

///
