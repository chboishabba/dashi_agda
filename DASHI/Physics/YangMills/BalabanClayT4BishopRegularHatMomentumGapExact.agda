module DASHI.Physics.YangMills.BalabanClayT4BishopRegularHatMomentumGapExact where

------------------------------------------------------------------------
-- ROUND88: ONE OUTER BISHOP COMPONENT -> FULL REGULAR WILSON GAP
--
-- PRIMARY SOURCES
--
-- Kenneth G. Wilson,
-- "Confinement of Quarks", Physical Review D 10 (1974), 2445--2459.
-- DOI: 10.1103/PhysRevD.10.2445.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Errett Bishop and Douglas Bridges,
-- "Constructive Analysis", Springer, 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- DASHI CONTRIBUTION
--
-- Every generated regular Brillouin cell has at least one outer coordinate.
-- The canonical Bishop Wilson atom is exactly
--
--   hat k^2 = sum_{mu=0}^3 4 sin^2(k_mu/2),
--
-- and every summand is constructively nonnegative.  Therefore a lower bound on
-- the ONE outer summand selected by the finite grid geometry is automatically a
-- lower bound on the complete four-dimensional denominator.
--
-- Combined with `BalabanBishopOuterBrillouinSineGapExact`, the intended physical
-- constant is
--
--       4 sin^2(k_outer/2) >= 7569/4096 > 0.
--
-- This file proves the structural four-dimensional compilation.  The remaining
-- physical trig seam is solely to identify the selected literal box sine with
-- the canonical Machin-period outer angle to which that 1D Bishop theorem
-- applies.  No 240-box denominator receipts remain.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_)

import Real as Bishop
import RealProperties as BishopP

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayT4GeneratedBrillouinGridExact as Grid
import DASHI.Physics.YangMills.BalabanClayT4RegularGridOuterAxisExact as Outer
import DASHI.Physics.YangMills.BalabanClayT4LiteralOneLoopBoxEvaluatorExact as Eval
import DASHI.Physics.YangMills.BalabanClayT4CanonicalBishopAtomEnvironmentExact as Canonical
import DASHI.Physics.YangMills.BalabanClayT4LiteralWilsonHatMomentumBishopIdentificationExact as Hat

scaled : Canonical.PhysicalTrigBoxData → Eval.MomentumRole → Eval.AxisIndex → Bishop.ℝ
scaled = Canonical.scaledSineSquareValue

scaledNonnegative : ∀ dataSet role axis →
  Bishop.NonNegative (scaled dataSet role axis)
scaledNonnegative dataSet role axis =
  Hat.scaledSquareNonnegative (Canonical.sineHalfValue dataSet role axis)

component0BelowHat : ∀ dataSet role →
  Bishop._≤_
    (scaled dataSet role Eval.axis0)
    (Canonical.hatMomentumValue dataSet role)
component0BelowHat dataSet role =
  let
    s0 = scaled dataSet role Eval.axis0
    s1 = scaled dataSet role Eval.axis1
    s2 = scaled dataSet role Eval.axis2
    s3 = scaled dataSet role Eval.axis3
    rest = s1 Bishop.+ (s2 Bishop.+ s3)
    restNN = BishopP.nonNegx,y⇒nonNegx+y
      (scaledNonnegative dataSet role Eval.axis1)
      (BishopP.nonNegx,y⇒nonNegx+y
        (scaledNonnegative dataSet role Eval.axis2)
        (scaledNonnegative dataSet role Eval.axis3))
    canonicalAsSelectedPlusRest :
      Bishop._≃_ (Canonical.hatMomentumValue dataSet role) (s0 Bishop.+ rest)
    canonicalAsSelectedPlusRest =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜ a ⊕ (b ⊕ (c ⊕ d)))
        BishopP.≃-refl s0 s1 s2 s3
    selectedBelowSelectedPlusRest : Bishop._≤_ s0 (s0 Bishop.+ rest)
    selectedBelowSelectedPlusRest =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ s0))
        (BishopP.+-monoʳ-≤ s0 (BishopP.nonNegx⇒0≤x restNN))
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm canonicalAsSelectedPlusRest)
    selectedBelowSelectedPlusRest

component1BelowHat : ∀ dataSet role →
  Bishop._≤_
    (scaled dataSet role Eval.axis1)
    (Canonical.hatMomentumValue dataSet role)
component1BelowHat dataSet role =
  let
    s0 = scaled dataSet role Eval.axis0
    s1 = scaled dataSet role Eval.axis1
    s2 = scaled dataSet role Eval.axis2
    s3 = scaled dataSet role Eval.axis3
    rest = s0 Bishop.+ (s2 Bishop.+ s3)
    restNN = BishopP.nonNegx,y⇒nonNegx+y
      (scaledNonnegative dataSet role Eval.axis0)
      (BishopP.nonNegx,y⇒nonNegx+y
        (scaledNonnegative dataSet role Eval.axis2)
        (scaledNonnegative dataSet role Eval.axis3))
    reordered :
      Bishop._≃_ (Canonical.hatMomentumValue dataSet role) (s1 Bishop.+ rest)
    reordered =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜ b ⊕ (a ⊕ (c ⊕ d)))
        BishopP.≃-refl s0 s1 s2 s3
    selectedBelow : Bishop._≤_ s1 (s1 Bishop.+ rest)
    selectedBelow =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ s1))
        (BishopP.+-monoʳ-≤ s1 (BishopP.nonNegx⇒0≤x restNN))
  in
  BishopP.≤-respʳ-≃ (BishopP.≃-symm reordered) selectedBelow

component2BelowHat : ∀ dataSet role →
  Bishop._≤_
    (scaled dataSet role Eval.axis2)
    (Canonical.hatMomentumValue dataSet role)
component2BelowHat dataSet role =
  let
    s0 = scaled dataSet role Eval.axis0
    s1 = scaled dataSet role Eval.axis1
    s2 = scaled dataSet role Eval.axis2
    s3 = scaled dataSet role Eval.axis3
    rest = s0 Bishop.+ (s1 Bishop.+ s3)
    restNN = BishopP.nonNegx,y⇒nonNegx+y
      (scaledNonnegative dataSet role Eval.axis0)
      (BishopP.nonNegx,y⇒nonNegx+y
        (scaledNonnegative dataSet role Eval.axis1)
        (scaledNonnegative dataSet role Eval.axis3))
    reordered :
      Bishop._≃_ (Canonical.hatMomentumValue dataSet role) (s2 Bishop.+ rest)
    reordered =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜ c ⊕ (a ⊕ (b ⊕ d)))
        BishopP.≃-refl s0 s1 s2 s3
    selectedBelow : Bishop._≤_ s2 (s2 Bishop.+ rest)
    selectedBelow =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ s2))
        (BishopP.+-monoʳ-≤ s2 (BishopP.nonNegx⇒0≤x restNN))
  in
  BishopP.≤-respʳ-≃ (BishopP.≃-symm reordered) selectedBelow

component3BelowHat : ∀ dataSet role →
  Bishop._≤_
    (scaled dataSet role Eval.axis3)
    (Canonical.hatMomentumValue dataSet role)
component3BelowHat dataSet role =
  let
    s0 = scaled dataSet role Eval.axis0
    s1 = scaled dataSet role Eval.axis1
    s2 = scaled dataSet role Eval.axis2
    s3 = scaled dataSet role Eval.axis3
    rest = s0 Bishop.+ (s1 Bishop.+ s2)
    restNN = BishopP.nonNegx,y⇒nonNegx+y
      (scaledNonnegative dataSet role Eval.axis0)
      (BishopP.nonNegx,y⇒nonNegx+y
        (scaledNonnegative dataSet role Eval.axis1)
        (scaledNonnegative dataSet role Eval.axis2))
    reordered :
      Bishop._≃_ (Canonical.hatMomentumValue dataSet role) (s3 Bishop.+ rest)
    reordered =
      let open BishopP.ℝ-Solver
      in solve 4
        (λ a b c d → a ⊕ b ⊕ c ⊕ d ⊜ d ⊕ (a ⊕ (b ⊕ c)))
        BishopP.≃-refl s0 s1 s2 s3
    selectedBelow : Bishop._≤_ s3 (s3 Bishop.+ rest)
    selectedBelow =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ s3))
        (BishopP.+-monoʳ-≤ s3 (BishopP.nonNegx⇒0≤x restNN))
  in
  BishopP.≤-respʳ-≃ (BishopP.≃-symm reordered) selectedBelow

record SelectedOuterBishopGap
    (dataSet : Canonical.PhysicalTrigBoxData)
    (role : Eval.MomentumRole)
    (cell : Grid.GridCell4) : Set₁ where
  field
    gap : Bishop.ℝ
    gapAtAxis0 : Grid.isInner (Grid.c0 cell) ≡ false →
      Bishop._≤_ gap (scaled dataSet role Eval.axis0)
    gapAtAxis1 : Grid.isInner (Grid.c1 cell) ≡ false →
      Bishop._≤_ gap (scaled dataSet role Eval.axis1)
    gapAtAxis2 : Grid.isInner (Grid.c2 cell) ≡ false →
      Bishop._≤_ gap (scaled dataSet role Eval.axis2)
    gapAtAxis3 : Grid.isInner (Grid.c3 cell) ≡ false →
      Bishop._≤_ gap (scaled dataSet role Eval.axis3)
open SelectedOuterBishopGap public

selectedOuterGapBelowHatMomentum :
  ∀ {dataSet role cell}
    (outerGap : SelectedOuterBishopGap dataSet role cell) →
  Grid.allInner cell ≡ false →
  Bishop._≤_ (gap outerGap) (Canonical.hatMomentumValue dataSet role)
selectedOuterGapBelowHatMomentum {dataSet} {role} {cell} outerGap regular
  with Outer.regularCellHasOuterAxis cell regular
... | Outer.outer0 proof = BishopP.≤-trans
  (gapAtAxis0 outerGap proof) (component0BelowHat dataSet role)
... | Outer.outer1 proof = BishopP.≤-trans
  (gapAtAxis1 outerGap proof) (component1BelowHat dataSet role)
... | Outer.outer2 proof = BishopP.≤-trans
  (gapAtAxis2 outerGap proof) (component2BelowHat dataSet role)
... | Outer.outer3 proof = BishopP.≤-trans
  (gapAtAxis3 outerGap proof) (component3BelowHat dataSet role)

regularBishopOuterGapToWilsonDenominatorLevel : ProofLevel
regularBishopOuterGapToWilsonDenominatorLevel = machineChecked

-- Physical one-dimensional weld only: for an outer axis of the literal box,
-- identify the SAME sine-half atom with the Machin-normalized angle and apply
-- the already-proved 7569/4096 Bishop outer-sine-square lower bound.
physicalSelectedOuterSineIsMachinAngleLevel : ProofLevel
physicalSelectedOuterSineIsMachinAngleLevel = conditional
