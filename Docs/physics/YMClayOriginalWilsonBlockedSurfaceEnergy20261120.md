### 20 November — constructor correction: literal Path13, not straight F19 holonomy

The straight-boundary estimate in YMClayOriginalWilsonBlockedSurfaceEnergy20261120.md applies to native ordered path blocking only. It is NOT a bound on the nonlinear CMP98 Eqs.(119)-(121) averaging operation; a side-13 square fixture is not a Path13 test. The actual owners are BalabanCMP98Path13BishopNativeSourceExact, BalabanCMP98Path13PrintedRoleSourceFamilyExact, BalabanCMP98Equation119TwoCarrierSelectedBondExact (assembledEquation120QSource), BalabanPath13RadiusOperatorDefectRouteExact, and BalabanCMP98Path13RelativeContourPrincipalImageExact. The latter already supplies the literal 74-factor contour budget 37/1024 conditional on the selected fine-link radius; do not rebuild it. NativeGeometry selects the background via BackgroundFieldVariationalTheorem, whose original fine-constraint/action identification and small-field admission remain explicit. Do not substitute the F19 straight map for that constraint.

Exact separation at identity: a fine axial link at axial offset zero but nonzero transverse offset has straight center-path differential zero and literal Eq120 coefficient 7/13^5 on a multiblock direction, or 1/13^4 on the one-block wrapped torus. Thus the constructors differ even at first order. Local SymPy executed scripts/check_ym_path13_constructor_boundary.py: six exact cyclic geometries, Gram SOS identity, column sums and overlap, and off-center derivative coefficient. The existing flat Gram is (113I+28(T+T^T))/13^6; independently its difference from 57I/13^6 is 28(I+T)(I+T^T)/13^6. This is corroboration, not new flat coercivity. Flat support overlaps at most two longitudinal blocks per fine axial link; nonlinear transverse contour contributions must not inherit that overlap without an actual incidence proof.

Next use actual selected variational background, complete Eq120 derivative and actual contour support/defect operators to inspect the nonflat operator budget and nonlinear RG marked activity. Do not promote the earlier straight surface transport to physical CMP116. This packet is a source/geometry correction and exact finite check, not a physical moment or spectral theorem; no Agda acceptance claimed.

# Original Wilson aligned blocked surface energy transport

20 November 2026. Source-specific analytic continuation of YMClayOriginalWilsonSparseChessboard20261120.md, reconciling the earlier YMClayOriginalWilsonSparseChessboardBidi20261119.md. Standard group norm/plaquette surface decomposition and chessboard inequality retain attribution; DASHI contribution is the explicit original-source transport and scale obstruction.

## Same-source construction

Use the ordered straight positive block paths of YMClayNativeBlockedPositiveHolonomyGaugeExact and YMClaySUNNativeBlockedPositiveHolonomyExact, not a new bare coarse measure. For coarse side M>=2 and integer block factor b>=1, fine side Mb, each aligned coarse plaquette P is the boundary of a b by b fine square. Its holonomy is an ordered product of b^2 conjugates of the fine plaquettes (possibly inverted if orientation changes). To see this, successively attach unit squares in rows: join each square base to the current boundary base by a path on the already attached complex; the shared edge words cancel against their inverses as the boundary is updated. Conjugations preserve the quaternion norm and inversions preserve deficit. Equivalently set horizontal links to identity by gauge transformation row by row, then telescope the vertical words, first across columns and then along the boundary product. Noncommutativity is retained.

For d(U)=1-ReTr(U)/2 on SU(2), norm(U-I)^2=2d(U). The unitary product telescoping norm bound and Cauchy-Schwarz yield
d_P^(b) <= b^2 sum_{p in P} d_p.
For distinct aligned coarse plaquettes, the fine squares are disjoint as sets of oriented-positive plaquette labels: the two varying fine coordinates have unique quotient/remainder decomposition, the other two are fixed multiples of b; distinct plane orientations have disjoint labels. Each coarse square contains b^2 labels. This works with periodic wrap.

Let A be m distinct aligned coarse plaquettes. Using the previous microscopic joint bound (conditional on the standard closed-cube chessboard applicability; conservatively restrict to dyadic compatible fine tori) gives for 0<=theta<=1/96:
E_{B_b*mu_beta} exp(theta beta/b^2 sum_A d_P^(b)) <= exp(C(beta) b^2 m/4).
This is the actual pushforward law by definition. For the specific b=2 F19 source, YMClayOriginalWilsonCanonicalBlockedMarkF19Exact is the existing marked-expectation identity; do not substitute the bare coarse state. The native all-scale effective-density and scalar-order weld remains to be checked.

Consequent probability for all marks exceeding eps is <= min(1,exp(-m kappa_b)), with kappa_b=beta eps/(96 b^2)-C(beta)b^2/4. Useful positivity requires beta eps>24 C(beta)b^4. For fixed b and fixed eps, eventually holds at large beta; for b growing like a^-1 at fixed physical diameter and logarithmic beta(a), fails. No uniform normalized physical block moment follows.

## Exact negative control

In an open b by b patch, choose commuting unit quaternions q_b=((1-t^2)/(1+t^2),2t/(1+t^2),0,0), t=1/b^2, horizontal links identity and vertical link at column x equal q_b^x. Each fine plaquette is q_b, d(q_b)=2/(b^4+1), while the boundary is q_b^(b^2), whose deficit tends to 1-cos(2)>0 by b^2 atan(1/b^2)->1. Hence even pointwise tiny microscopic deficit cannot imply tiny blocked deficit uniformly in block factor. This is a local deterministic configuration, not a Gibbs probability claim or a periodic uniform-flux assignment. The b^2 surface-loss scaling is of the correct order for this deterministic method. Neither this nor absence of a useful bound proves failure of physical clustering.

## CMP116 boundary

BalabanLiteralTwoWilsonCMP116ConnectingTailExact consumes actual differentiated cluster charges and chargeSumBelowRootedTail. Our probability bounds concern fixed-threshold geometric events, not mixed derivatives of the marked polymer expansion. No bound on those charges follows absent a source-specific domination and control of good-region propagations. Next reuse actual nonlinear CMP116/CMP119 marked-propagator and renormalized activity bounds to supply that consumer; do not introduce an independent cluster law. Historical round identifiers are provenance.

## Local exact checks

Executed scripts/check_ym_blocked_surface_energy.py locally with output: PASS: 120 noncommuting surface fixtures, 4 periodic incidence fixtures, 5 Abelian flux controls, 1 symbolic rate identity. The fixtures use exact rational SU(2) quaternions; not Haar integration or proof of chessboard applicability. No Agda kernel run or new Agda declarations. No Clay gate promoted.
