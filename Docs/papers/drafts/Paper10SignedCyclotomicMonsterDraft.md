# Exact cyclotomic intertwiners for finite Heisenberg representations: signed polarization transport and Monster normalizer recognition

Working Paper 10 candidate — 2026-11-20. TOE #1217 mathematical owner. Not a submission.

## Abstract
We investigate exact polarization transport for the two nontrivial central characters of the finite Heisenberg group over F3 with six position coordinates. Dependent binary support/sign fibres, native 729-state charts and cyclotomic kernels encode selected source-derived symplectic and anti-symplectic transformations. The selected ATLAS 2.Suz:2 matrix action gives a mirror-adapted Fourier rotation and a rank-five chart change with 243 nonzero coefficients per row and column in the reported model. Full Monster multiplicity recognition is a distinct source-dependent problem. We specify complete character-table and quotient-descent acceptance conditions for it.

## 1. Signed geometry
Binary support identifies opposite trits; the full sign fibre is lossless. The support fibre of weight k has size 2^k, yielding 3^n=sum binom(n,k)2^k. Reuse BalancedTritBitFibre, the dihedral codec and native zeta54/729 BIDI maps. Cardinality equivalence does not establish action equivalence. The 3C residual comparison is distinct from the 3B recognition problem.

## 2. Selected Heisenberg and Weil model
For c((a,b),(a',b'))=b.a', use W_s(a,b,z)e_x=zeta^(s(z+b.x))e_(x+a). A similitude A with multiplier lambda has quadratic correction q(x)=2x^T(A^T C A-lambda C)x over F3. The selected source mirror has adapted form diag(I,-I); the rotation has off-diagonal blocks U,V with UV=-I and symmetric U,V. F_s(y,x)=zeta^(s y^T V x)/27 intertwines the generators and squares to parity. Paired conjugate phases give a D4 model. These instantiate standard Weil theory, not a novelty claim for the general theory.

## 3. Coordinate change
A=Pa^-1 P has reported upper-right rank5. The modulation vacuum and its translated columns give a sparse cyclotomic matrix with 243 nonzeros per column. Encode zero coefficients separately from root exponents. The normalization 1/[9(1+2 zeta^s)] has squared magnitude 1/243. See the TOE ledger and check_toe_atlas_mirror.py, check_toe_atlas_weil.py, check_toe_atlas_rechart.py. Exact dependency replay and independent composed-matrix regression remain outstanding.

## 4. Suzuki multiplicity selection
Under actual sector premises the multiplicity Hom_E(H_s,W_s) has dimension90. The faithful 12 plus faithful78 candidate has central C2 trace -90; the faithful 12 plus Sym²12 candidate has trace +66. Neither dimension nor central phase identifies the original selected 78. Reuse #1250 full-character selection at c6a86e955baead05eef8dfe1a1c0f22d5b81de41: 6.Suz restriction from 6.Suz.2, main-group inflation, exact decomposition, quotient MN3B descent, Monster occurrence. The 210-class 6.Suz audit matches all class values, complete class signatures, power maps, runtime versions and literal Irr indices. The original class20 quotient kernel matters. No actual output receipt recovered in this round. Finite-field quotient matrices do not specify the complex multiplicity representation.

## 5. Acceptance and scope
Canonical execution ledger: docs/superpowers/plans/2026-10-16-dashi-toe-universal-realization-ledger.md. Paper 8 cites the finite package; Paper 9 remains independent. Complete source selection, both actual linear Hom maps, actual mirror compatibility, pinned Agda acceptance, and literature novelty audit remain open. No physical realization claimed.

## References and attribution
Barraclough and Wilson (2007), DOI 10.1112/S1461157000001352; Nebe (2025), DOI 10.1007/s10801-025-01399-2; ATLAS/AtlasRep original matrices; DASHI #1098/#1250 source producers. JMD centralizer/North Star diagrams and smoothness observations; DASHI signed geometry and source transport; joint model/character comparison. Preserve Ibrahim and JFine source-specific ownership. Full bibliography and novelty audit pending.

## 6. Direct original-coordinate regression (2026-11-20)
The selected finite model now has a direct composed-matrix test, not just a conjugation proof. In the cyclotomic coefficient-pair basis (a,b) representing a+b*zeta, multiplication is (ac-bd,ad+bc-bd). Write k and f for the unnormalized positive-phase rechart and Fourier kernels. The rotation numerator is k† f k with denominator 243*27=6561; the positive-to-negative mirror numerator is -k^T k with denominator243 (the conjugate normalization has opposite sign). Verify all original-chart Weyl generator covariance equations, with each source multiplier and quadratic central correction. Local execution of check_toe_atlas_composed.py passed 25,509,168 entry comparisons and exact rotation parity, unitarity, mirror involution and dihedral equations. Original rotation has 729 nonzeros per column; original mirror has 81 (rank-four mixing), rechart 243 (rank-five mixing), adapted mirror one. This is a source-selected finite computational certificate and a candidate sparse transport case study, not a new general Weil theorem. Actual 90-dimensional Suzuki multiplicity action and original Monster linear Hom evaluation are still unrecognized; GAP/Nix absent locally, no authentic 210-class receipt or kernel check. Existing source authors and donor owners unchanged.
