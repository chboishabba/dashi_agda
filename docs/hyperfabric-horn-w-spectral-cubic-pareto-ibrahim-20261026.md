# Exact SU(3) selected-W spectral cubic and source-local horn meridian max-cut
Date: 2026-10-26, Australia/Brisbane.
Repository owner: Agda PR #1249; cross-prover scalar mirror: Lean PR #84.
Status: EXACT CALCULATIONS EXECUTED locally (independent equivalent Python);
committed GitHub source present, NOT byte-for-byte executed here;
native Lean/Agda sources written, no kernel checks. Not a physical experiment.

## Attribution: first-link mathematics and existing repo owners

1. J. W. Alexander (1924), original wild sphere, DOI 10.1073/pnas.10.1.8.
2. Allen Hatcher, *Algebraic Topology*, Example 2B.2, original *marked*
   injective F_(2^n) commutator tower of the horned complement.
   No numerical loop lengths or gauge connection norm is supplied there.
3. Morikuni Gotô (1949), DOI 10.2969/jmsj/00130270:
   every element of compact connected semisimple SU3 is a commutator.
   This gives the abstract positive recursive representation
   previously implemented in Agda neutrino PR #1247, not a geometry.
4. **Agda neutrino PR #1247 is the actual OWNER of selected W**, its
   exact Q(zeta3) trace and synthetic charged-flavour fixture.
   The generic unitary spectral theorem, Cayley-Hamilton and Newton
   identities are classical, not new authorship claims here.
5. Agda horn PR #1244 is the original 3-sector SAME-OBJECT geometry
   owner, now with an explicit pierced-shell open-ball overlap product,
   a central pi1 paper argument and an honest relative collar
   acceptance ledger. Its source and provenance remain independent.
6. Earlier Agda #1249 and Lean #84 derive the sharp direct SU3
   commutator norm cap and prior W gap lower bound.
   This cut adds an EXACT tighter consequence of the pre-existing
   cyclotomic trace, NOT a new W or new original SU3 trace theorem.
7. Exotic-topology Agda #1254 and Lean #86 are useful NEGATIVE/CW
   donors; different ambient wild embeddings cannot be identified by
   the same binary Cantor address or finite linked cartoon.

## Characteristic polynomial source-to-exact calculation

Original selected root (same W as neutrino #1247) has trace

    T=tr W=(176093404722400-19836986431118*zeta)
             /181846007130841,
    zeta=-1/2+i*sqrt(3)/2.

Thus both t=Re(T) and u²=(Im(T))² are EXACT rational values:

    D=181846007130841,
    t=(176093404722400+19836986431118/2)/D,
    u²=3*(19836986431118)²/(4 D²).

For W in SU3, lambda_i lie on the unit circle and satisfy
lambda_1 lambda_2 lambda_3=1. The SU3 characteristic identity
`tr(W²)=T²-2 conjugate(T)` follows from the second elementary
symmetric function e2(W)=det(W)*tr(W^-1)=conjugate(T).

Define the positive semidefinite Hermitian
`X=(W-I)^*(W-I)=2I-W-W^*` with spectral values
`x_j=|lambda_j-1|²`. By direct Newton identities,

    sum_j x_j = 2(3-t),
    sum_{i<j} x_i x_j = (3-t)²+u²=|3-T|²,
    product_j x_j=|det(I-W)|²=4u².

Consequently the EXACT cubic is

    p_X(x) = x³-2(3-t)x²+((3-t)²+u²)x-4u².

This last expression uses only the original Q(zeta3) trace, the
original determinant-one/unitarity theorem for W, and classical
matrix identities. No eigenvalue numerics are needed for the proof.

For q=517/250=2.068:

    p_X(q) =
      -78609668791519322720866577865447
       /516687036084841809701458863765625000 <0.

Since p_X(q)=product_j(q-x_j), and all three x_j are REAL,
negativity implies at least one x_j>q (otherwise each factor >=0).
Thus we have the NEW exact selected-root spectral receipt

    ||W-I||op² > 517/250.

This REPLACES as strongest available source-specific bound the
previous weaker Frobenius/trace result
`||W-I||op² >= 854996726408/648677790003`.
Do not claim the previous inequality is false; it remains true.

### New immediate first-generation flat SU3 child obstruction

The prior directly sharp unitary commutator arc theorem is

    d([A,B])² <= 4s²-s⁴ when d(B)<=s<=sqrt(2),

and symmetrically for A. The right hand side is monotone on
0<=s<=sqrt(2). At s=781/1000,

    4s²-s⁴ = q-208421521/10^12 < q.

Therefore for any SAME-OBJECT *FLAT*, correctly Hatcher-marked
W=[A,B] in SU3,

    d(A)>781/1000,   d(B)>781/1000.

This is a necessary property of an already-existing ABSTRACT
representation, not evidence of a short source meridian or of
a physical neutrino observable.

### More generous curved one-stage acceptance

For one correctly Hatcher-marked child with d(child)<=3/4,
the same direct arc theorem gives the exact strict comparison

    d([A,B])² <=495/256 < (1391/1000)².

The selected W satisfies

    d(W)²>517/250>(1437/1000)².

If a GENUINE BASED parent-to-commutator homotopy for the SAME
unitary connection produces a curved Wilson defect eta<=23/500,
the unitary triangle inequality yields

    d(W) <= d([A,B])+eta
         < 1391/1000+23/500
         = 1437/1000 <d(W), CONTRADICTION.

Thus **one marked child d<=3/4 AND one real eta<=23/500** reject
this selected W. Flat eta=0 is a special case. This is a stronger
acceptance window than the earlier d(child)<=3/5, eta<=3/1000.
No source 3D homotopy or curvature-area value has been produced.

### Independent local calculation and negative controls

`scripts/check_horn_w_exact_spectral_cubic_maxcut.py`
reconstructs t,u² in exact Python Fraction; checks the full
negative rational cubic value, the child-arc margin and curved
rational inequalities. It also independently reconstructs the
same source W using the already selected #1247 rational PMNS
fixture; numerical squared singular gaps are approximately

    0.00919734, 1.87659879, 2.06838609.

The numerical values are cross-checks, NOT used to deduce
the strictly rational >2.068 certificate. A source-conditional
negative control with child d=4/5 is NOT rejected by this
necessary single-child bound.

Lean #84 source-writing:
`Integration/DASHITOE/HornSelectedWSpectralCubicCut.lean`
contains exact rational trace definitions, cubic inequality,
a spectral-factorization-to-large-eigenvalue conditional theorem,
flat 781/1000 and curved 23/500 scalar rejection.
The analytic SU3 matrix-to-cubic theorem and actual source
holonomy inputs remain EXTERNAL until kernel-supplied;
this is NOT a Lean kernel proof of the operator norm result.

## Latest PR inspiration and P0 actual source geometry

The recent horn owner #1244 now has
`Docs/topology/AlexanderHornedC3ExplicitExteriorOpenCover20261025.md`
and `scripts/alexander_horned_c3_pierced_shell_product.py`.
Its satellite shell \(15/4<r<17/4\) with one removed straight
spoke is explicitly homeomorphic to interval times open disk.
This closes a finite cover-overlap *paper* step. It **does not**
construct the Hatcher stage-one generator loops or certify that
any arbitrary small circle avoids the FULL linked X_1 stage.
Do not duplicate the owner's central van Kampen or collar algebra.

Hatcher's nested compact X_n implies a local meridian lying outside
the entire X_n automatically remains in the limiting open exterior,
with positive clearance if its image is compact. Existing #1244
C3 rigid rotations transport lengths/clearances across sectors.

For the DIRECT selected W test, a tiny UNBASED local loop suffices
for the NORM gap even if a based whisker is long: after verifying
the actual Hatcher free-group generator conjugacy in the SAME
exterior, transport from the global basepoint changes its unitary
holonomy by conjugation, preserving ||U-I||. The local metric
connection bound needs only the tiny loop's length, not the
whisker's; the conjugacy/marking is a separate topological obligation.

The actual outstanding P0 source witness is therefore:
* one real first-generation Hatcher generator/conjugacy class;
* source Euclidean embedding for its local rectifiable representative;
* proof that its image avoids ALL of the linked finite-stage X_1;
* metric length L and compatible actual connection coefficient M.

A flat source meeting M L<=781/1000 would be inconsistent with
the selected W. A curved source meeting ML<=3/4 and genuine
based eta<=23/500 would likewise be inconsistent.

The words *finite source stage*, *marked generator*, *C3 rotation*,
*unitary local transport*, and *curvature-based eta* name DISTINCT
contracts. Their conjunction, not another synthetic matrix, is
the remaining physical/geometric discriminant.

## Ibrahim / Pareto next-owner stop rule

1. ORIGINAL provenance roots and reprints must not multiply the
   evidence count. Attribute Hatcher's topology, Gotô's existence,
   classical SU3 algebra, #1247's W, #1244's geometry and this
   selected-W exact consequence to their respective source owners.
2. P0 is the **same-object** linked first-stage meridian with
   whole-stage avoidance and source local length, not a new C3
   abstract representation or finite-link negative-control fixture.
3. P1 is one **based** source homotopy with transported curvature
   integral and area (not a merely homotopic abstract group word).
4. P2 is a source-selected gauge/matter action and independent
   observable. A flat bundle from abstract monodromy is NOT a
   bounded gauge potential, curvature singularity or lepton mass
   mechanism. Preserve ordinary-ring control.
5. P3 is actual Lean/Agda kernel verification of these new
   theorem files; neither compiler nor CI was run in this cut.

No fake QIDs, Dewey entries, measured physical data, CI green
status or absent geometric witness are to be promoted.


## Scale-covariant same-source negative control (2026-10-26)

For any fixed actual smooth unitary connection source, applying a
spatial homothety by factor s>0 and transporting that SAME connection
as a differential one-form changes a Euclidean local loop
L -> L'=sL and its operator coefficient bound M -> M'=M/s.
For the corresponding homotopy area and curvature norm,
Area -> Area'=s² Area, K -> K'=K/s². Consequently

    M' L' = M L,             K' Area' = K Area.

Therefore arbitrary resizing of the horn's stage coordinates is NOT
by itself evidence that the selected W can or cannot be produced.
The physical energy/field regularity assumptions must be paid
independently. Holding numerical M constant under s->0 would change
the physical connection, NOT passively transport the original source.

Exact rational negative-control source:
`scripts/check_horn_homothety_source_scale_no_go.py`,
locally equivalent Fraction checks PASS at six scales (1/10^6,
1/100, 1/2, 1, 2, 100). No metric, source connection or experimental
data for the true Hatcher stage is created by the calculation.

This modifies the **interpretation**, not the mathematical correctness,
of the flat ML<=781/1000 and curved
ML<=3/4, eta<=23/500 acceptance tests. Both are dimensionless,
same-source tests; their premise cannot be manufactured solely by
coordinate scaling. The local UNBASED meridian conjugacy distinction
and true relative cap/collar topology remain the P0 obligations.
