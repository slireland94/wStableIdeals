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
    "palpVertices","getVerticesFromWS", "getWSFromDim",
    }



-- directory: "C:\Users\Seth\OneDrive - Colostate\Documents\GitHub\wStableIdeals"

--------------------------------------------------------
--------------------------------------------------------
-- CONSTRUCTING W-STABLE IDEALS
--------------------------------------------------------
--------------------------------------------------------


psiMap = (S,R,degs) -> (
    L = {};
    for i from 1 to numgens S do (
    L = append(L,y_i^(degs_(i-1)));
    );
    psi = map(R,S,L)
    )

wBorelClosure = (I,w) -> (
    S := ring I;
    K := coefficientRing S;
    n := numgens S;
    R := K[y_1..y_n];
    I := monomialIdeal I;
    psi := psiMap(S,R,w);
    psI := monomialIdeal psi(I);
    psIbar := borel psI;
    Ibar := preimage_psi(psIbar)
    )



/// Example: The weight vector of all ones gives the classic Borel Closure
K = ZZ/101;
w = {1,1,1};
n = #w;
S = K[x_1..x_n,Degrees=>w];
R = K[y_1..y_n];
psi = psiMap(S,R,w)
Bgensw = {x_1*x_2*x_3^2};
Ibar = wBorelClosure(ideal(Bgensw),w)

///
