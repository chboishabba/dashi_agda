# Programme attribution and 369 cross-domain reuse contract — 2026-11-20

Standing research rule requested by the programme owner. Precedent: PR #1444
(head d182ad5b3c192149df2df9d618e5f4e78fbb77c6), especially its source-first,
same-object, original-author and finite-vs-continuum gates. This document
extends the policy across PR #1530, NS369, YM369, EM/Filsinger, GR-QFT and
subsequent work. It does not modify ESD or transfer third-party ownership.

## Mandatory claim receipt

For each material result record: claim ID; original authors and primary
source identifier (DOI/arXiv or exact repository path and commit);
source statement and hypotheses; existing internal owner(s); actual new
delta and contributor provenance; target carrier, units, orientation and
normalization; transfer map and equality/commutation obligations;
evidence actually executed; negative controls; open obligations.
Secondary exposition and user-suggested research directions are separately
attributed. Never infer authorship from repository ownership, never identify
an unverified remembered author with a different paper, and never claim an
existing theorem as a novel DASHI discovery. Preserve Ibrahim/Monster3B,
ESD and prior contributor attribution as in #1444.

Evidence levels are independent: external theorem under its hypotheses;
source-written formalization; exact symbolic/reference execution;
byte-verified local execution; pinned Agda kernel acceptance; continuum
theorem; physical calibration/experiment. Report the actual level, not the
strongest aspirational label. Agda is the golden formal target. Neither
CI nor an exact numerical example alone closes continuum physics.
Search original owners before implementing; inspect source rather than
merely descriptions; preserve same-source negative controls. No silent
imports across unmerged branches.

## Canonical reuse crosswalk

Reference master 116cd7de01b8a0da03703b3bb8db79c67fd15b50 inspected:

- DASHI/Physics/Foundations/OrientedBracketEMYMNS369Regression.agda:
  existing orientation bridge, imports EM RightHandRule369Exact,
  YM SU2Bracket369OrientationBridgeExact, NS NSCross369OrientationBridgeExact.
  Pure quaternion su(2) bracket is twice cross product. Spatial vs internal
  gauge indices differ; 3 components do not establish physical identity.
- DASHI/Physics/YangMills/BalabanC3MonsterEquivarianceAuditExact.agda:
  literal spatial C3 and source seam gates; #1444 extends actual side-four
  Wilson signed path and six plane source transport. Reuse same selected
  carrier; Haar/Gibbs and continuum claims remain separately gated.
- DASHI/Physics/Closure/NSCriticalConeResidualFibre369CrossPollinationExact.agda:
  actual finite counterexample to signed coherence descending through shell
  observation, not an actual NSE solution.
- DASHI/Core/ThreeChannelC3EquivarianceGateExact.agda: require intertwiner,
  not merely three channels. AdS ell=0,2,4 with distinct radial dimensions
  are not a physical cyclic symmetry merely because indexed by 0,1,2.
- Docs/physics/DiamondYM369C3NSFourierOpticalMaxCut20261024.md:
  prior optical signed interference reuse of NS division-free covariance.
  Extend to complex Hermitian Gram on the identical gravitational kernel
  carrier, preserving phase and relative signs.
- Docs/physics/KSW668F8PhysicalConstraintRadialSobolevMaxCut20261115.md:
  original radial stiffness powers commute with the finite linear generator;
  reuse for exact eigenmode propagation, NOT nonlinear GR commutation.
- Docs/research/ns_r734_phase_curvature_369_20261027.md:
  same-source full Galerkin phase and weighted transfers; use diagnostics,
  do not import NS interaction coefficients into Einstein equations.
- Base369 hyperfabric holonomy is explicitly a finite analogue; selected
  physical gauge-valued map required before treating it as Wilson holonomy.

## Geometric reuse gates

For each candidate map J between carriers, first classify as coordinate
codec, common algebra, equivariant map, same-object operator transport,
or physical equivalence. An equivariance claim requires J rho(g) =
rho'(g) J on the actual actions; operator transport requires J L = L' J
on the stated domain; a coarse observer P is sufficient only if the
consumer O factors as Obar P. Otherwise preserve residual information.
Do not equate Euclidean YM, Lorentzian GR, fluid vorticity and EM field
strength. Compare curvature, oriented brackets, gauge-covariant transport,
phase, shell weights, signed residual and conservation structures with
the correct indices, signatures and physical units. Prefer shared
implementations and explicit counterexamples over duplicate abstractions.

## External GR turbulence attribution

Bizon/Rostworowski (2011), DOI 10.1103/PhysRevLett.107.031102:
numerical Einstein-massless-scalar AdS instability and conjectured
resonant mixing. Bizon/Rostworowski (2017), DOI 10.5506/APhysPolB.48.1375:
numerical purely gravitational AdS5 collapse in biaxial Bianchi IX ansatz.
Hunik-Kostyra/Rostworowski (2020), DOI 10.1007/JHEP06(2020)002:
resonant system in that gravitational ansatz. Huneau/Luk (2024),
DOI 10.1088/1361-6382/ad5487: high-frequency Einstein solutions and
Burnett/backreaction literature. These are original external research,
not DASHI discoveries. The user's remembered Unger GR-QFT source remains
unresolved; do not substitute other authors or claim identification.
No theorem transfer to the moving Poincare brane without checking
boundary, gauge, resonance, source and geometry hypotheses.

## Implementation priorities

1. Exact separated radial eigenmode propagation on the existing finite
   operator; compare native forward and adjoint, retain checkpoint resume.
2. Same-carrier Hermitian Gram/phase ledger using existing NS/optical
   covariance and residual-observer owners, with spectral derivative norms.
3. Joint radial/normal/time refinement and actual source moments;
   do not discard UV modes to manufacture apparent convergence.
4. Time-indexed Filsinger Maxwell/charged matter: select fluid, kinetic or
   microscopic closure from actual regime and source. Retain Poynting and
   matter work, boundary flux and total stress-energy conservation.
5. Nonlinear Einstein source derive actual interaction coefficients and
   resonant transfer; distinguish forcing, linear geometry, coherent
   observation, numerical dispersion and physical nonlinear cascade.
6. Physical detector normalization and empirical validation remain open.

This is a policy and source crosswalk, not a new numerical solver, Agda
kernel receipt, turbulence proof or Clay closure.
