{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNR650SingleSelfCompleteOrbitCollapseRound716Exact where

------------------------------------------------------------------------
-- ROUND716 / COMPLETE ONE-COPY SELF ORBIT = THREE COPIES OF ONE GLOBAL ROW SUM
--
-- R715 shows there is no naive ROW-LOCAL fibre transport between the three
-- outer energy legs.  On the COMPLETE physical enumeration, however, R38
-- supplies exact permutations for pEnergyLeg and qEnergyLeg.
--
-- Therefore for the arbitrary scalar function
--
--   f(beta) = maskedSingleOuterRow(beta),
--
-- the complete sums satisfy
--
--   sum_beta f(pEnergyLeg beta) = sum_beta f(beta),
--   sum_beta f(qEnergyLeg beta) = sum_beta f(beta).
--
-- Since R714's one-copy orbit residue is
--
--   f(beta) + f(pEnergyLeg beta) + f(qEnergyLeg beta),
--
-- its complete fold is exactly
--
--   CompleteSingleSelfOrbit = 3 * CompleteMaskedSingleSelfRows.
--
-- This is decisive bookkeeping: cyclic reindexing alone does NOT provide an
-- additional signed cancellation.  Exact self cancellation is now equivalent
-- to cancellation of the one global masked selected-self row sum.
--
-- No estimate, norm, or sign claim is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadOrbitConstruction as Orbit
import DASHI.Physics.Closure.NSTriadKNPhysicalGalerkinIncidencePermutationRound38Exact as R38
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNLiteralViscousQuadraticCoefficientRound30Exact as Field30
import DASHI.Physics.Closure.NSTriadKNR650GlobalCommutatorNestedTriadExpansionRound694Exact as R694
import DASHI.Physics.Closure.NSTriadKNR650SingleSelfCommutatorOrbitRound714Exact as R714

three : ℚ
three = 3

module CompleteCollapse
    (physicalSystem : Field30.PhysicalFiniteComplex3GalerkinSystem R694.F)
    (S : Helical.HelicalModeScalars R694.F)
    (L : Helical.PeriodicHelicalProjectorLaws R694.F
      (Field30.physicalEmbedding physicalSystem)
      (Field30.physicalInverseSquare physicalSystem) S)
    (H : R142.HelicalHalfCalibration S)
    (velocityTransverse :
      (mode : Z3.FourierMode) →
      Helical.Transverse
        (Field30.physicalEmbedding physicalSystem)
        mode
        (Audit.velocity (Field30.finiteSystem physicalSystem) mode)) where

  module One =
    R714.SingleSelfOrbit physicalSystem S L H velocityTransverse

  items : List Physical.PhysicalTriadIncidence
  items =
    Physical.physicalTriadEnumeration
      One.Carrier.Split.Full.Nested.Base.cutoff

  foldMaskedSingleRows : ℚ
  foldMaskedSingleRows =
    R38.foldPower One.maskedSingleOuterRow items

  pLegFoldIsBase :
    R38.foldPower
      (λ beta → One.maskedSingleOuterRow (Orbit.pEnergyLeg beta))
      items
    ≡ foldMaskedSingleRows
  pLegFoldIsBase =
    trans
      (sym
        (R38.foldMap
          One.maskedSingleOuterRow Orbit.pEnergyLeg items))
      (R38.foldPermutationInvariant
        One.maskedSingleOuterRow
        (R38.pEnergyLegEnumerationPermutation
          One.Carrier.Split.Full.Nested.Base.cutoff))

  qLegFoldIsBase :
    R38.foldPower
      (λ beta → One.maskedSingleOuterRow (Orbit.qEnergyLeg beta))
      items
    ≡ foldMaskedSingleRows
  qLegFoldIsBase =
    trans
      (sym
        (R38.foldMap
          One.maskedSingleOuterRow Orbit.qEnergyLeg items))
      (R38.foldPermutationInvariant
        One.maskedSingleOuterRow
        (R38.qEnergyLegEnumerationPermutation
          One.Carrier.Split.Full.Nested.Base.cutoff))

  foldOrbitSplitsThree :
    (xs : List Physical.PhysicalTriadIncidence) →
    R38.foldPower One.singleOrbitResidue xs
    ≡
    R38.foldPower One.maskedSingleOuterRow xs
      + R38.foldPower
          (λ beta → One.maskedSingleOuterRow (Orbit.pEnergyLeg beta)) xs
      + R38.foldPower
          (λ beta → One.maskedSingleOuterRow (Orbit.qEnergyLeg beta)) xs
  foldOrbitSplitsThree [] = solve []
  foldOrbitSplitsThree (beta ∷ rest) =
    trans
      (cong₂ _+_
        refl
        (foldOrbitSplitsThree rest))
      (solve
        ( One.maskedSingleOuterRow beta
        ∷ One.maskedSingleOuterRow (Orbit.pEnergyLeg beta)
        ∷ One.maskedSingleOuterRow (Orbit.qEnergyLeg beta)
        ∷ R38.foldPower One.maskedSingleOuterRow rest
        ∷ R38.foldPower
            (λ selected →
              One.maskedSingleOuterRow (Orbit.pEnergyLeg selected)) rest
        ∷ R38.foldPower
            (λ selected →
              One.maskedSingleOuterRow (Orbit.qEnergyLeg selected)) rest
        ∷ []))

  completeSingleSelfOrbitIsThreeGlobalRows :
    One.foldSingleOrbit items
    ≡ three * foldMaskedSingleRows
  completeSingleSelfOrbitIsThreeGlobalRows =
    trans
      (foldOrbitSplitsThree items)
      (trans
        (cong₂ _+_
          (cong₂ _+_ refl pLegFoldIsBase)
          qLegFoldIsBase)
        (solve (foldMaskedSingleRows ∷ [])))

------------------------------------------------------------------------
-- Status.
------------------------------------------------------------------------

round716CompleteSingleSelfOrbitIsThreeGlobalMaskedRows : Bool
round716CompleteSingleSelfOrbitIsThreeGlobalMaskedRows = true

round716CyclicPermutationAloneCreatesSelfCancellation : Bool
round716CyclicPermutationAloneCreatesSelfCancellation = false

round716RemainingSelfExactQuestionIsGlobalMaskedRowCancellation : Bool
round716RemainingSelfExactQuestionIsGlobalMaskedRowCancellation = true

round716IntroducesEstimate : Bool
round716IntroducesEstimate = false

round716SelfOrbitExactCancellationClosed : Bool
round716SelfOrbitExactCancellationClosed = false

round716ClayPromotion : Bool
round716ClayPromotion = false

round716CompleteSingleSelfOrbitIsThreeGlobalMaskedRowsIsTrue :
  round716CompleteSingleSelfOrbitIsThreeGlobalMaskedRows ≡ true
round716CompleteSingleSelfOrbitIsThreeGlobalMaskedRowsIsTrue = refl

round716CyclicPermutationAloneCreatesSelfCancellationIsFalse :
  round716CyclicPermutationAloneCreatesSelfCancellation ≡ false
round716CyclicPermutationAloneCreatesSelfCancellationIsFalse = refl

round716RemainingSelfExactQuestionIsGlobalMaskedRowCancellationIsTrue :
  round716RemainingSelfExactQuestionIsGlobalMaskedRowCancellation ≡ true
round716RemainingSelfExactQuestionIsGlobalMaskedRowCancellationIsTrue = refl

round716IntroducesEstimateIsFalse :
  round716IntroducesEstimate ≡ false
round716IntroducesEstimateIsFalse = refl

round716SelfOrbitExactCancellationClosedIsFalse :
  round716SelfOrbitExactCancellationClosed ≡ false
round716SelfOrbitExactCancellationClosedIsFalse = refl

round716ClayPromotionIsFalse :
  round716ClayPromotion ≡ false
round716ClayPromotionIsFalse = refl
