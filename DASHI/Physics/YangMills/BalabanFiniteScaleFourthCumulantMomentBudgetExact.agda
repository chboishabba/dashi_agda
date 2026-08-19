module DASHI.Physics.YangMills.BalabanFiniteScaleFourthCumulantMomentBudgetExact where

------------------------------------------------------------------------
-- ROUND66/68: SIGNED FINITE-SCALE FOURTH-CUMULANT MOMENT BUDGET
--
-- PRIMARY SOURCE / CALIBRATION
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed.
-- DOI: 10.1007/978-1-4612-4728-9.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record FourthCumulantMomentBudget : Set₁ where
  field
    fourPoint pair12_34 pair13_24 pair14_23 fourthCumulant : ℚ
    fourthCumulantExact :
      fourthCumulant
      ≡ fourPoint - pair12_34 - pair13_24 - pair14_23
    fourPointLower pair12_34Upper pair13_24Upper pair14_23Upper : ℚ
    fourPointLowerSound : fourPointLower ≤ fourPoint
    pair12_34UpperSound : pair12_34 ≤ pair12_34Upper
    pair13_24UpperSound : pair13_24 ≤ pair13_24Upper
    pair14_23UpperSound : pair14_23 ≤ pair14_23Upper
open FourthCumulantMomentBudget public

signedMomentLower : FourthCumulantMomentBudget → ℚ
signedMomentLower dataSet =
  fourPointLower dataSet
  - pair12_34Upper dataSet
  - pair13_24Upper dataSet
  - pair14_23Upper dataSet

fourthCumulantAboveSignedMomentLower :
  (dataSet : FourthCumulantMomentBudget) →
  signedMomentLower dataSet ≤ fourthCumulant dataSet
fourthCumulantAboveSignedMomentLower dataSet =
  let
    neg12 = ℚP.neg-mono-≤ (pair12_34UpperSound dataSet)
    neg13 = ℚP.neg-mono-≤ (pair13_24UpperSound dataSet)
    neg14 = ℚP.neg-mono-≤ (pair14_23UpperSound dataSet)

    summed = ℚP.+-mono-≤
      (ℚP.+-mono-≤
        (ℚP.+-mono-≤ (fourPointLowerSound dataSet) neg12)
        neg13)
      neg14

    lowerNormal :
      fourPointLower dataSet
        + (- pair12_34Upper dataSet)
        + (- pair13_24Upper dataSet)
        + (- pair14_23Upper dataSet)
      ≡ signedMomentLower dataSet
    lowerNormal = ℚRing.solve-∀
      (fourPointLower dataSet)
      (pair12_34Upper dataSet)
      (pair13_24Upper dataSet)
      (pair14_23Upper dataSet)

    actualNormal :
      fourPoint dataSet
        + (- pair12_34 dataSet)
        + (- pair13_24 dataSet)
        + (- pair14_23 dataSet)
      ≡ fourthCumulant dataSet
    actualNormal = trans
      (ℚRing.solve-∀
        (fourPoint dataSet)
        (pair12_34 dataSet)
        (pair13_24 dataSet)
        (pair14_23 dataSet))
      (sym (fourthCumulantExact dataSet))
  in
  subst
    (λ left → left ≤ fourthCumulant dataSet)
    lowerNormal
    (subst
      (λ right →
        fourPointLower dataSet
          + (- pair12_34Upper dataSet)
          + (- pair13_24Upper dataSet)
          + (- pair14_23Upper dataSet)
        ≤ right)
      actualNormal
      summed)

record BufferedFourthCumulantMomentBudget : Set₁ where
  field
    budget : FourthCumulantMomentBudget
    interactionMargin continuumError : ℚ
    signedMomentLeavesBuffer :
      interactionMargin + continuumError ≤ signedMomentLower budget
open BufferedFourthCumulantMomentBudget public

finiteFourthCumulantHasContinuumBuffer :
  (dataSet : BufferedFourthCumulantMomentBudget) →
  interactionMargin dataSet + continuumError dataSet
  ≤ fourthCumulant (budget dataSet)
finiteFourthCumulantHasContinuumBuffer dataSet =
  ℚP.≤-trans
    (signedMomentLeavesBuffer dataSet)
    (fourthCumulantAboveSignedMomentLower (budget dataSet))

fourthCumulantSignedMomentCompilerLevel : ProofLevel
fourthCumulantSignedMomentCompilerLevel = machineChecked

physicalFiniteFourPointLowerLevel : ProofLevel
physicalFiniteFourPointLowerLevel = conditional

physicalFinitePairingUpperLevels : ProofLevel
physicalFinitePairingUpperLevels = conditional
