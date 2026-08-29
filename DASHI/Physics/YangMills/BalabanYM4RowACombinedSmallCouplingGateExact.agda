module DASHI.Physics.YangMills.BalabanYM4RowACombinedSmallCouplingGateExact where

------------------------------------------------------------------------
-- ROW A: ONE SMALL-COUPLING INEQUALITY PAYS BOTH NUMERICAL GATES
--
-- Master already isolates the two numerical requirements
--
--   C gamma < b                         (positive shell margin)
--   L gammaTube < b - C gamma          (shooting contraction).
--
-- On a coupling tube with gammaTube <= gamma, it is enough to prove the single
-- source-facing inequality
--
--                  (C + L) gamma < b.
--
-- This module proves that implication exactly over the ordered rationals.
-- Hence, once the literal Gaussian floor b is positive and the literal source
-- derivative constants C,L are finite, Row A does not require two unrelated
-- numerical searches: both gates are paid by the same sufficiently-small
-- coupling choice.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _≤_; _<_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanP33RationalQuaternionNormSquaredExact as Norm

record CombinedRowASmallCouplingGate : Set where
  field
    gaussianFloor interactionConstant derivativeBound : ℚ
    couplingCap tubeWidth : ℚ

    interactionConstantNonnegative : 0ℚ ≤ interactionConstant
    derivativeBoundNonnegative : 0ℚ ≤ derivativeBound
    couplingCapNonnegative : 0ℚ ≤ couplingCap
    tubeWidthNonnegative : 0ℚ ≤ tubeWidth
    tubeWidthBelowCouplingCap : tubeWidth ≤ couplingCap

    combinedSmallness :
      (interactionConstant + derivativeBound) * couplingCap
      < gaussianFloor

open CombinedRowASmallCouplingGate public

interactionPartBelowCombined :
  (dataSet : CombinedRowASmallCouplingGate) →
  interactionConstant dataSet * couplingCap dataSet
  ≤ (interactionConstant dataSet + derivativeBound dataSet)
      * couplingCap dataSet
interactionPartBelowCombined dataSet =
  let
    C = interactionConstant dataSet
    L = derivativeBound dataSet
    g = couplingCap dataSet

    cBelowSum : C ≤ C + L
    cBelowSum =
      subst
        (λ right → C ≤ right)
        (ℚP.+-identityʳ C)
        (ℚP.+-monoʳ-≤ C (derivativeBoundNonnegative dataSet))
  in
  Norm.scaleʳ-nonNeg
    (couplingCapNonnegative dataSet)
    cBelowSum

combinedSmallnessGivesSignGate :
  (dataSet : CombinedRowASmallCouplingGate) →
  interactionConstant dataSet * couplingCap dataSet
  < gaussianFloor dataSet
combinedSmallnessGivesSignGate dataSet =
  ℚP.≤-<-trans
    (interactionPartBelowCombined dataSet)
    (combinedSmallness dataSet)

combinedSmallnessGivesDerivativePlusInteraction :
  (dataSet : CombinedRowASmallCouplingGate) →
  derivativeBound dataSet * couplingCap dataSet
    + interactionConstant dataSet * couplingCap dataSet
  < gaussianFloor dataSet
combinedSmallnessGivesDerivativePlusInteraction dataSet =
  let
    C = interactionConstant dataSet
    L = derivativeBound dataSet
    g = couplingCap dataSet
    combined = combinedSmallness dataSet
  in
  subst
    (λ left → left < gaussianFloor dataSet)
    (ℚRing.solve-∀ C L g)
    combined

combinedSmallnessGivesShootingGateAtCap :
  (dataSet : CombinedRowASmallCouplingGate) →
  derivativeBound dataSet * couplingCap dataSet
  < gaussianFloor dataSet
      - interactionConstant dataSet * couplingCap dataSet
combinedSmallnessGivesShootingGateAtCap dataSet =
  let
    Cg = interactionConstant dataSet * couplingCap dataSet
    Lg = derivativeBound dataSet * couplingCap dataSet
    summed = combinedSmallnessGivesDerivativePlusInteraction dataSet

    shifted : Lg + Cg - Cg < gaussianFloor dataSet - Cg
    shifted = ℚP.+-monoʳ-< (- Cg) summed
  in
  subst
    (λ left → left < gaussianFloor dataSet - Cg)
    (ℚRing.solve-∀ Lg Cg)
    shifted

combinedSmallnessGivesShootingGate :
  (dataSet : CombinedRowASmallCouplingGate) →
  derivativeBound dataSet * tubeWidth dataSet
  < gaussianFloor dataSet
      - interactionConstant dataSet * couplingCap dataSet
combinedSmallnessGivesShootingGate dataSet =
  let
    L = derivativeBound dataSet
    tube = tubeWidth dataSet
    cap = couplingCap dataSet

    tubeScaled : L * tube ≤ L * cap
    tubeScaled = Norm.scaleNonnegative
      L (derivativeBoundNonnegative dataSet)
      (tubeWidthBelowCouplingCap dataSet)
  in
  ℚP.≤-<-trans
    tubeScaled
    (combinedSmallnessGivesShootingGateAtCap dataSet)

rowACombinedSmallnessToSignGateLevel : ProofLevel
rowACombinedSmallnessToSignGateLevel = machineChecked

rowACombinedSmallnessToShootingGateLevel : ProofLevel
rowACombinedSmallnessToShootingGateLevel = machineChecked

-- Physical seam after this reduction: identify finite source constants C,L and
-- the literal positive Gaussian floor b on one admissible source tube; choose
-- the source small-coupling threshold so (C+L)gamma<b.  No second independent
-- shooting-smallness search is mathematically required.
literalRowACombinedSmallCouplingInstantiationLevel : ProofLevel
literalRowACombinedSmallCouplingInstantiationLevel = conditional
