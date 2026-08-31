{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP98Equation119YIndexedDexpRound154Exact where

------------------------------------------------------------------------
-- ROUND154 A1 BIDI: ONE Y-INDEXED DEXP FAMILY, OUTER Y DERIVED FROM THE BLOCK
--
-- Primary source:
-- Tadeusz Bałaban, "Averaging Operations for Lattice Gauge Theories",
-- Commun. Math. Phys. 98 (1985), 17--51. DOI: 10.1007/BF01211042.
--
-- Immediately before Eq. (119), CMP98 defines the point variables Y_x and then
-- says
--
--     Y = sum_{x in B(c-)} L^{-d} Y_x.
--
-- Round153 fixed the signs of the printed g/g^{-1} operators, but Round148's
-- general convention could still choose unrelated LR records at the outer Y and
-- at every point Y_x.  That is more freedom than the source has.
--
-- Here the public source supplies only the point values Y_x.  The outer Y is
-- constructed by the SAME exact radius-six block sum and 1/28561 weight already
-- used in Round147.  A single Lie-calculus family
--
--     atY : Lie -> LeftRightDexpCancellationData Lie
--
-- is then evaluated at those values.  Thus neither the outer LR record nor the
-- point LR records are independently selectable.
--
-- This is a BIDI least-privilege reduction: after Round154 the remaining
-- physical Lie seam is the source meaning of Y_x itself (principal log of the
-- literal relative contour/background object) plus identification of ONE
-- existing LR calculus family on the Lie carrier.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanCMP98MultiscaleAveragingDerivativeRound126Exact as R126
import DASHI.Physics.YangMills.BalabanCMP98Equation119OneStepDerivativeRound146Exact as R146
import DASHI.Physics.YangMills.BalabanCMP98Equation119LiteralPathRound147Exact as R147
import DASHI.Physics.YangMills.BalabanCMP98Equation119DexpReuseRound148Exact as R148
import DASHI.Physics.YangMills.BalabanCMP98Equation119LeastPrivilegeSourceRound152Exact as R152
import DASHI.Physics.YangMills.BalabanCMP109LeftRightInverseDexpCancellationExact as LR
import DASHI.Physics.YangMills.BalabanClayGate4CMP109CenteredOddBlockCarrierExact as Centered
import DASHI.Physics.YangMills.BalabanPeriodicTorus4Carrier as Carrier

record CMP98Equation119PointYFamily
    {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) : Set₁ where
  field
    pointY :
      Nat → Centered.CenteredBlockPoint4 6 →
      R126.Vector (R146.additive C)

open CMP98Equation119PointYFamily public

record UniformLeftRightDexpFamily (Lie : Set) : Set₁ where
  field
    atY : Lie → LR.LeftRightDexpCancellationData Lie

open UniformLeftRightDexpFamily public

scaledPointYTerms :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98Equation119PointYFamily source →
  Nat → List (Centered.CenteredBlockPoint4 6) →
  List (R126.Vector (R146.additive C))
scaledPointYTerms source yFamily step [] = []
scaledPointYTerms source yFamily step (point ∷ points) =
  R152.scaleV source R147.siteWeightℚ (pointY yFamily step point)
  ∷ scaledPointYTerms source yFamily step points

-- Literal CMP98 definition Y = sum_x L^{-d} Y_x at the minimal source scale.
outerY :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98Equation119PointYFamily source →
  Nat → R126.Vector (R146.additive C)
outerY source yFamily step =
  R146.sumV
    (scaledPointYTerms source yFamily step
      (Carrier.elements (Centered.centeredBlockFinite 6)))

asYIndexedDexpConvention :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98Equation119PointYFamily source →
  UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  R148.CMP98Equation119DexpConvention (R126.Vector (R146.additive C))
asYIndexedDexpConvention source yFamily calculus = record
  { R148.CMP98Equation119DexpConvention.outer =
      λ step → atY calculus (outerY source yFamily step)
  ; R148.CMP98Equation119DexpConvention.atPoint =
      λ step point → atY calculus (pointY yFamily step point)
  }

pointConventionIsSingleFamilyAtYx :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (yFamily : CMP98Equation119PointYFamily source)
    (calculus : UniformLeftRightDexpFamily (R126.Vector (R146.additive C)))
    step point →
  R148.atPoint (asYIndexedDexpConvention source yFamily calculus) step point
  ≡ atY calculus (pointY yFamily step point)
pointConventionIsSingleFamilyAtYx source yFamily calculus step point = refl

outerConventionIsSingleFamilyAtDerivedY :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group)
    (yFamily : CMP98Equation119PointYFamily source)
    (calculus : UniformLeftRightDexpFamily (R126.Vector (R146.additive C)))
    step →
  R148.outer (asYIndexedDexpConvention source yFamily calculus) step
  ≡ atY calculus (outerY source yFamily step)
outerConventionIsSingleFamilyAtDerivedY source yFamily calculus step = refl

yIndexedLeastPrivilegeOneStepDerivative :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98Equation119PointYFamily source →
  UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  R126.OneStepAveragingDerivative (R146.additive C)
yIndexedLeastPrivilegeOneStepDerivative source yFamily calculus =
  R152.leastPrivilegeOneStepDerivative source
    (asYIndexedDexpConvention source yFamily calculus)

yIndexedLeastPrivilegeMultiscaleDerivative :
  ∀ {C n Value group}
    (source : R152.LiteralEquation119LeastPrivilegeSource C n Value group) →
  CMP98Equation119PointYFamily source →
  UniformLeftRightDexpFamily (R126.Vector (R146.additive C)) →
  Nat → R126.Operator (R146.additive C)
yIndexedLeastPrivilegeMultiscaleDerivative source yFamily calculus =
  R152.leastPrivilegeMultiscaleDerivative source
    (asYIndexedDexpConvention source yFamily calculus)

cmp98Equation119OuterYBlockAverageRound154Level : ProofLevel
cmp98Equation119OuterYBlockAverageRound154Level = machineChecked

cmp98Equation119SingleYIndexedDexpFamilyRound154Level : ProofLevel
cmp98Equation119SingleYIndexedDexpFamilyRound154Level = machineChecked

-- Remaining source-facing Lie seam after Round154:
--   * pointY really is CMP98's Y_x, i.e. the principal logarithm of the literal
--     relative contour/background group element used in the source;
--   * `atY` is the already-owned physical left/right dexp calculus uniformly
--     evaluated at that Lie value.
-- The outer Y and all outer/point LR record choices are downstream constructions.
literalCMP98PointYPrincipalLogIdentificationRound154Level : ProofLevel
literalCMP98PointYPrincipalLogIdentificationRound154Level = conditional

literalCMP98UniformYIndexedDexpFamilyRound154Level : ProofLevel
literalCMP98UniformYIndexedDexpFamilyRound154Level = conditional
