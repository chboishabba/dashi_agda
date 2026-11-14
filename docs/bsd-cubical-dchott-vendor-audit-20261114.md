# BSD K1–K5: pinned Cubical/DCHoTT vendor reuse audit
## 14 November 2026 — original Agda and Lean source, not claimed terminal BSD

### Verified pinned external sources

Direct repository and *exact pinned commit* inspections:

- `flake.nix` pins `felixwellen/DCHoTT-Agda`
  `ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e`.
- `flake.nix` pins `agda/cubical`
  `d0b9c7b0e9e4f816422c3447d7983b03274dd829`.
- `dashi-agda.agda-lib` declares
  `standard-library`, `dchott-agda` and `cubical-0.9`.
- `DASHI/Geometry/DCHoTTImportShim.agda` already imports
  DCHoTT `EqualityAndPaths`, `FormalDisk`, `Im`, `Manifolds`,
  `G-structure`; explicitly splits `--cohesion` and `--cubical`.
- `DASHI/Physics/QFT/AQFTCubicalQuotientSurface.agda`
  already contains a REAL optional Cubical set-quotient surface:
  `_/_`, `[_]`, `eq/`, `squash/`, under
  `{-# OPTIONS --cubical --guardedness #-}`.
  This is a useful **existing proof donor**; do not implement
  another generic set-quotient socket.

### Exact mathematical vendor declarations

Pinned `Cubical/HITs/SetQuotients/Base.agda`:
  `_/_`, `[_]`, `eq/`, `squash/`.

Pinned `Cubical/HITs/SetQuotients/Properties.agda`:
  `rec`, `setQuotUniversal`,
  `setQuotBinOp`, `setQuotUnaryOp`.
  These could realize the actual quotient
  `Q* / (Q*)²` as a Cubical set quotient and transport operations,
  ONCE the original noncubical relation is admitted on a compatible
  cubical carrier. The currently constructed Agda
  `RationalSquareClassSetoidExact` and
  `EllipticRationalKummerOpenExact` remain authoritative;
  the new Cubical quotient must not be mislabelled an identity
  with those types without an actual equivalence and proof.

Pinned `Cubical/Algebra/AbGroup/Base.agda`:
  `AbGroup`, `AbGroupHom`, `AbGroupEquiv`.
  Could package E[2], Kummer cochains or a Selmer abelian group,
  but it has no actual continuous Galois H¹,
  local Kummer equivalence or Sha LES in the searched sources.

Pinned `Cubical/Algebra/Group/Abelianization/Properties.agda`:
  explicit abelianization universal property, not an elliptic
  Galois-cohomology long exact sequence.
Pinned `Cubical/Algebra/OrderedCommMonoid/PropCompletion.agda`
  constructs an ORDERED MONOID PROPOSITIONAL completion; this
  is NOT Bishop ℝ, Cauchy-complete reals or a positive integral.

Pinned DCHoTT source exposes formal disks, cohesion,
homogeneous structures and G-structures, but no
original curve Kummer H¹, local `Q₂` points, Dedekind eta,
Mellin modularity or classical Sha(E).

### Flag/cross-carrier safety

The original noncubical arithmetic owner
`EllipticRationalKummerOpenExact.agda` does not declare
`--cubical-compatible`; the existing DCHoTT shim
explicitly documents `--cohesion` vs `--cubical`
incompatibility. No new BSD cubical wrapper is therefore
silently imported by the authoritative noncubical
K1/K2/K3/K4 Agda proof graph.

To use Cubical here, first produce (in a separately
compiled `--cubical` lane):
  A) exact original `Q*/(Q*)²` setoid carrier and relation import
     accepted under compatible flags, OR an independent cubical
     presentation plus a separately proved same-object equivalence;
  B) operation transport and explicit Kummer compatibility square;
  C) actual local H¹ realization if seeking K1/K2.
  None is currently inhabited by the vendor alone.

### Strict gate audit

- K1: Cubical set quotient MAY streamline **representation**
  of rational square classes; it does NOT prove real/Q₂
  Kummer images or Galois-cohomological naturality.
- K2: Cubical abelian groups MAY streamline abstract exact
  sequence interfaces; no classical global/local continuous
  Galois H¹ or `Sha(E)[2]` comparison donor located.
- K3: Neither vendor replaces Michael Stoll's ACTUAL
  `WeierstrassCurve.Affine.fg_point_of_numberField` nor
  the original `P=T+2U` argument. Lean PR #107 owns the
  finite-generation adapter, with root Lean/mathlib version
  mismatch and local acceptance pending.
- K4: Neither vendor supplies the selected curve
  `η(4τ)²η(8τ)²` analytic newform, eta inversion, or Mellin.
  Use actual pinned Mathlib `ModularForm.eta_ne_zero`
  and differentiability, and Agda Bishop as the golden
  ordered-real semantics. The new Lean PR #107
  `cmLevel32EtaAnalyticExpression_imaginary_pos_of_real`
  proves strict positivity of the LITERAL analytic expression
  given precisely the two eta-factor reality identities.
  This reduces remaining positivity debt to reality of
  actual eta on the imaginary axis; the independent
  modularity and Mellin equalities remain open.
- K5: Higher quotients/univalence do NOT imply
  odd-primary `Sha`, full leading-coefficient BSD,
  or universal BSD.

### New K0 repair on Lean PR #107

`scripts/bsd_local_maxcut_verify.sh` at prior PR head
was syntactically corrupted: an unfinished `mathlib_pin`
assignment ran directly into the body and the module list
and axiom block were duplicated. It has been REPLACED by
a fail-closed local checker that:
  - checks actual pinned mathlib v4.28.0 and expected
    Lean 4.28 toolchain, with explicit shell-only override
    because the root toolchain pins Lean 4.35-rc3;
  - builds 29 original selected-curve Synthesis sources,
    including the new actual analytic eta positivity theorem;
  - runs explicit `#print axioms` targets and fails on `sorryAx`.
This is a genuine verification-interface repair, not a
successful Lean kernel receipt: neither `lake` nor `agda`
is installed in the current execution container.
The exact script still needs a local `bash -n` and genuine
toolchain build before it can be described as accepted.

### Maximum cut: exact remaining mathematical producer names

K1 `originalRatSquareClassSignAndV2Invariant`;
`actualQ2E2H1KummerImageEquiv`;
`actualRealE2H1KummerImageEquiv`;
`allFinitePlacesKummerRestrictionNaturality`.

K2 `actualContinuousEBarDoublingKummerLES`;
`classicalShaTwoEquivExplicitSelmerCokernel`;
`localEBarCompletionCoefficientComparison`.

K3 `originalMWStollLocalKernelAccepted`;
`originalModTwoRankReductionLocalKernelAccepted`;
`originalEGroupAgdaLeanSameObjectEquivalence`.

K4 `actualEtaImaginaryAxisRealness`;
`originalLevel32EtaCuspForm`;
`dimS2Gamma0_32_eq_one`;
`originalELevel32NormalizedNewformIdentity`;
`originalBishopEtaMellinCentralValue`;
`originalEtaPositiveTailIntegral`.

K5 `actualOddPrimaryShaArithmetic`;
`samePeriodTamagawaShaLeadingCoefficient`;
`universalBSD` (unresolved research conjecture).

All names in this last block are **ROADMAP TARGETS**, not asserted
pre-existing qualified Agda/Lean constants. The actual named
source proofs and donor declarations are cited above.
