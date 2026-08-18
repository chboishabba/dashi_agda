module DASHI.Physics.YangMills.YangMillsContinuumFourthCumulantNonGaussianExact where

------------------------------------------------------------------------
-- MATHEMATICAL CONTEXT
--
-- For a centred Gaussian field, Wick's rule determines the four-point moment
-- entirely from pairings of two-point moments, so the connected/truncated
-- fourth function vanishes.  Consequently a single gauge-invariant observable
-- quadruple with a strictly nonzero fourth cumulant is already a sufficient
-- non-Gaussian / interacting witness.  This is much weaker than an area law
-- and is therefore the higher-alpha target for the Clay nontriviality seam.
--
-- DASHI CONTRIBUTION
--
-- Make that implication exact over the rational comparison carrier used for
-- quantitative Schwinger-function enclosures.  If
--
--   kappa4 = S4 - (S2_12 S2_34 + S2_13 S2_24 + S2_14 S2_23)
--
-- has |kappa4| bounded below by a positive margin, Wick factorization is
-- impossible.  The module deliberately does NOT import the adversarial
-- Schwinger--Dyson claim as authority; the remaining physical theorem is the
-- same-observable continuum lower bound itself.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; _+_; _-_; _*_; _<_; _≤_; ∣_∣)
import Data.Rational.Properties as ℚP
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Relation.Nullary.Negation.Core using (¬_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

record FourPointMomentData : Set where
  constructor fourPointMoments
  field
    S4 : ℚ
    S2-12 S2-34 S2-13 S2-24 S2-14 S2-23 : ℚ
open FourPointMomentData public

wickPairingSum : FourPointMomentData → ℚ
wickPairingSum dataSet =
  S2-12 dataSet * S2-34 dataSet
  + S2-13 dataSet * S2-24 dataSet
  + S2-14 dataSet * S2-23 dataSet

fourthCumulant : FourPointMomentData → ℚ
fourthCumulant dataSet = S4 dataSet - wickPairingSum dataSet

GaussianWickFour : FourPointMomentData → Set
GaussianWickFour dataSet = S4 dataSet ≡ wickPairingSum dataSet

wickFourImpliesFourthCumulantZero :
  ∀ dataSet → GaussianWickFour dataSet → fourthCumulant dataSet ≡ 0ℚ
wickFourImpliesFourthCumulantZero dataSet wick =
  subst
    (λ selected → selected - wickPairingSum dataSet ≡ 0ℚ)
    (sym wick)
    (ℚRing.solve-∀ (wickPairingSum dataSet))

absoluteZeroExact : ∣ 0ℚ ∣ ≡ 0ℚ
absoluteZeroExact = ℚP.∣0∣

positiveMarginCannotBoundZero : ∀ margin →
  0ℚ < margin → ¬ (margin ≤ 0ℚ)
positiveMarginCannotBoundZero margin marginPositive marginBelowZero =
  let
    impossible : margin < margin
    impossible = ℚP.≤-<-trans marginBelowZero marginPositive
  in
  ⊥-elim (ℚP.<-irrefl refl impossible)

record StrictFourthCumulantWitness (dataSet : FourPointMomentData) : Set where
  field
    margin : ℚ
    marginPositive : 0ℚ < margin
    marginBelowCumulant : margin ≤ ∣ fourthCumulant dataSet ∣
open StrictFourthCumulantWitness public

strictFourthCumulantImpliesNonzero :
  ∀ {dataSet} → StrictFourthCumulantWitness dataSet →
  ¬ (fourthCumulant dataSet ≡ 0ℚ)
strictFourthCumulantImpliesNonzero {dataSet} witness cumulantZero =
  let
    marginBelowZero : margin witness ≤ 0ℚ
    marginBelowZero =
      subst
        (λ upper → margin witness ≤ upper)
        (trans (cong ∣_∣ cumulantZero) absoluteZeroExact)
        (marginBelowCumulant witness)
  in
  positiveMarginCannotBoundZero
    (margin witness) (marginPositive witness) marginBelowZero

strictFourthCumulantRefutesGaussianWick :
  ∀ {dataSet} → StrictFourthCumulantWitness dataSet →
  ¬ GaussianWickFour dataSet
strictFourthCumulantRefutesGaussianWick {dataSet} witness wick =
  strictFourthCumulantImpliesNonzero witness
    (wickFourImpliesFourthCumulantZero dataSet wick)

record ContinuumGaugeInvariantFourthCumulantWitness : Set₁ where
  field
    Observable : Set
    observable1 observable2 observable3 observable4 : Observable
    moments : FourPointMomentData
    strictWitness : StrictFourthCumulantWitness moments
open ContinuumGaugeInvariantFourthCumulantWitness public

continuumFourthCumulantWitnessIsNonGaussian :
  ∀ witness → ¬ GaussianWickFour (moments witness)
continuumFourthCumulantWitnessIsNonGaussian witness =
  strictFourthCumulantRefutesGaussianWick (strictWitness witness)

fourthCumulantNonGaussianCriterionLevel : ProofLevel
fourthCumulantNonGaussianCriterionLevel = machineChecked

continuumGaugeInvariantNonGaussianAssemblyLevel : ProofLevel
continuumGaugeInvariantNonGaussianAssemblyLevel = machineChecked

-- Remaining physical nontriviality producer: for one fixed gauge-invariant
-- observable quadruple, prove that the actual continuum Schwinger moments are
-- the moments above and provide a strictly positive lower enclosure for
-- |kappa4|.  A Schwinger--Dyson identity is one possible producer, but is not
-- accepted merely because an adversarial preprint claims it.
physicalContinuumFourthCumulantLowerBoundLevel : ProofLevel
physicalContinuumFourthCumulantLowerBoundLevel = conditional
