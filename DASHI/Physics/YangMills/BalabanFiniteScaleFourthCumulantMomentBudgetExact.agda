module DASHI.Physics.YangMills.BalabanFiniteScaleFourthCumulantMomentBudgetExact where

------------------------------------------------------------------------
-- ROUND66: SIGNED FINITE-SCALE FOURTH-CUMULANT MOMENT BUDGET
--
-- PRIMARY SOURCE / CALIBRATION
--
-- James Glimm and Arthur Jaffe,
-- "Quantum Physics: A Functional Integral Point of View", 2nd ed.
-- DOI: 10.1007/978-1-4612-4728-9.
--
-- DASHI CONTRIBUTION
--
-- Leaf L9 previously asked directly for a strict finite-scale connected
-- fourth-cumulant margin.  For centered observables the connected four-point
-- function is the signed combination
--
--   kappa4 = M1234 - P12|34 - P13|24 - P14|23.
--
-- Therefore a rigorous lower bound should preserve that sign structure:
-- lower-bound the full four-point moment, upper-bound each disconnected pairing,
-- and subtract the three upper bounds only at the end.  No absolute-value
-- majorisation of the whole cumulant is needed.
--
-- The theorem below proves that these four finite enclosures plus ONE final
-- coefficient comparison give the exact delta+epsilon buffer consumed by the
-- Round65 same-limit margin transport.
------------------------------------------------------------------------

open import Data.Rational.Base as ℚ using (ℚ; _+_; _-_; _≤_)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (subst)

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
    actualNormal =
      let exact = fourthCumulantExact dataSet
      in
      subst
        (λ right →
          fourPoint dataSet
            + (- pair12_34 dataSet)
            + (- pair13_24 dataSet)
            + (- pair14_23 dataSet)
          ≡ right)
        exact
        (ℚRing.solve-∀
          (fourPoint dataSet)
          (pair12_34 dataSet)
          (pair13_24 dataSet)
          (pair14_23 dataSet))
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

-- Physical finite calculation after Round66: one lower enclosure for the
-- literal four-point function and three upper enclosures for the disconnected
-- pair products, all on the same finite-scale RG state/observable quadruple.
physicalFiniteFourPointLowerLevel : ProofLevel
physicalFiniteFourPointLowerLevel = conditional

physicalFinitePairingUpperLevels : ProofLevel
physicalFinitePairingUpperLevels = conditional
