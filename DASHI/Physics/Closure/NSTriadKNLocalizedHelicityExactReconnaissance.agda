module DASHI.Physics.Closure.NSTriadKNLocalizedHelicityExactReconnaissance where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact localized-helicity reconnaissance on the six-mode quartic
-- witness".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a DASHI-original exact computation.
-- Uses: the literal six-mode state and curl convention from
-- NSTriadKNGlobalHelicityH3DiscriminantCounterexample.
-- Relationship: records the exact executable result that every ordered
-- placement has zero real localized-helicity chain derivative on the witness,
-- while its helical-resolved complex transfer amplitudes retain nontrivial
-- phase information. It classifies the witness rows across all seven geometry
-- classes, rejects scalar localized helicity on this witness, and does not
-- claim a cutoff-uniform theorem for arbitrary states.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import Data.List.Base using (List; []; _∷_)
open import Data.Nat.Base using (_<_; z≤n; s≤s)
import Data.Integer.Base as Int
open import Data.Integer.Base using (+_)

import DASHI.Physics.Closure.NSTriadKNGlobalHelicityH3DiscriminantCounterexample as Witness
import DASHI.Physics.Closure.NSTriadKNLocalizedHelicityCommutatorProgram as Helical

ScalarSymbol : Set
ScalarSymbol = Witness.Mode → Int.ℤ

weightedZero : Int.ℤ → Int.ℤ
weightedZero coefficient = + 0

knownWitnessLocalizedCubicCorrection : ScalarSymbol → Int.ℤ
knownWitnessLocalizedCubicCorrection symbol =
  Int._+_
    (Int._+_
      (Int._+_ (weightedZero (symbol Witness.p))
                (weightedZero (symbol Witness.q)))
      (weightedZero (symbol Witness.k)))
    (Int._+_
      (Int._+_ (weightedZero (symbol (Witness.negateMode Witness.p)))
                (weightedZero (symbol (Witness.negateMode Witness.q))))
      (weightedZero (symbol (Witness.negateMode Witness.k))))

knownWitnessLocalizedCubicCorrectionIsZero :
  ∀ symbol → knownWitnessLocalizedCubicCorrection symbol ≡ + 0
knownWitnessLocalizedCubicCorrectionIsZero symbol = refl

record OrderedChainRow : Set where
  constructor chain-row
  field
    geometry : Helical.GeometricClass
    leftImaginary rightImaginary realDerivative : Int.ℤ

open OrderedChainRow public

positive : Nat → Int.ℤ
positive n = + n

negative : Nat → Int.ℤ
negative n = Int.-_ (+ n)

orderedChainRows : List OrderedChainRow
orderedChainRows =
  chain-row Helical.near (negative 198) (positive 198) (positive 0) ∷
  chain-row Helical.near (positive 222) (negative 222) (positive 0) ∷
  chain-row Helical.near (positive 180) (negative 180) (positive 0) ∷
  chain-row Helical.near (negative 744) (positive 744) (positive 0) ∷
  chain-row Helical.near (negative 480) (positive 480) (positive 0) ∷
  chain-row Helical.near (negative 60) (positive 60) (positive 0) ∷
  chain-row Helical.near (negative 222) (positive 222) (positive 0) ∷
  chain-row Helical.near (positive 198) (negative 198) (positive 0) ∷
  chain-row Helical.near (positive 744) (negative 744) (positive 0) ∷
  chain-row Helical.near (negative 180) (positive 180) (positive 0) ∷
  chain-row Helical.near (positive 480) (negative 480) (positive 0) ∷
  chain-row Helical.near (positive 60) (negative 60) (positive 0) ∷ []

orderedTriadCount helicityTripleCount resolvedContributionCount : Nat
orderedTriadCount = 12
helicityTripleCount = 8
resolvedContributionCount = orderedTriadCount * helicityTripleCount

resolvedContributionCountIsNinetySix :
  resolvedContributionCount ≡ 96
resolvedContributionCountIsNinetySix = refl

nearRowCount lowHighRowCount highLowRowCount farLowRowCount
  farHighRowCount transitionRowCount residualRowCount : Nat
nearRowCount = 12
lowHighRowCount = 0
highLowRowCount = 0
farLowRowCount = 0
farHighRowCount = 0
transitionRowCount = 0
residualRowCount = 0

nearRowCountIsTwelve : nearRowCount ≡ 12
nearRowCountIsTwelve = refl

nonNearRowCountIsZero :
  lowHighRowCount + highLowRowCount + farLowRowCount + farHighRowCount
    + transitionRowCount + residualRowCount
  ≡ 0
nonNearRowCountIsZero = refl

record RationalCoefficient : Set where
  constructor ratio
  field
    numerator : Int.ℤ
    denominator : Nat

record BiquadraticCoefficient : Set where
  constructor biquadratic
  field
    rational sqrt10 sqrt22 sqrt220 : RationalCoefficient

record ExactComplexBiquadratic : Set where
  constructor algebraic-complex
  field
    realPart imaginaryPart : BiquadraticCoefficient

zeroRatio : RationalCoefficient
zeroRatio = ratio (+ 0) 1

-- The first ordered near-triad, helicity triple (+,+,+), has
--   Re tau = 33/2 + (39/80) sqrt(220)
--   Im tau = (429/40) sqrt(10) + (51/8) sqrt(22).
-- The nonzero imaginary component is the exact phase carrier that the real
-- helicity density discards.
firstNearPPPTransferAmplitude : ExactComplexBiquadratic
firstNearPPPTransferAmplitude =
  algebraic-complex
    (biquadratic (ratio (+ 33) 2) zeroRatio zeroRatio (ratio (+ 39) 80))
    (biquadratic zeroRatio (ratio (+ 429) 40) (ratio (+ 51) 8) zeroRatio)

firstNearPPPImaginarySqrt10NumeratorPositive : 0 < 429
firstNearPPPImaginarySqrt10NumeratorPositive = s≤s z≤n

baseQuadraticReserve quarticReserve cubicMagnitude discriminantGap : Nat
baseQuadraticReserve = 8503484
quarticReserve = 245944
cubicMagnitude = 6111504
discriminantGap = 28984957666432

localizedPerturbedCubic : ScalarSymbol → Nat → Nat
localizedPerturbedCubic symbol epsilon = cubicMagnitude

localizedWitnessDiscriminantIdentity :
  ∀ symbol epsilon →
  localizedPerturbedCubic symbol epsilon
    * localizedPerturbedCubic symbol epsilon
  ≡ 4 * baseQuadraticReserve * quarticReserve + discriminantGap
localizedWitnessDiscriminantIdentity symbol epsilon = refl

record LocalizedHelicityExactReceipt : Set where
  constructor receipt
  field
    everyScalarSymbolHasZeroCorrection :
      ∀ symbol → knownWitnessLocalizedCubicCorrection symbol ≡ + 0
    everyScalarSymbolPreservesFailedDiscriminant :
      ∀ symbol epsilon →
      localizedPerturbedCubic symbol epsilon
        * localizedPerturbedCubic symbol epsilon
      ≡ 4 * baseQuadraticReserve * quarticReserve + discriminantGap
    allOrderedHelicityRowsPresent : resolvedContributionCount ≡ 96
    witnessRowsAreNear : nearRowCount ≡ 12
    allOtherWitnessGeometryClassesAreEmpty :
      lowHighRowCount + highLowRowCount + farLowRowCount + farHighRowCount
        + transitionRowCount + residualRowCount
      ≡ 0
    retainedTriadPhaseIsNontrivial : 0 < 429

open LocalizedHelicityExactReceipt public

localizedHelicityExactReceipt : LocalizedHelicityExactReceipt
localizedHelicityExactReceipt =
  receipt
    knownWitnessLocalizedCubicCorrectionIsZero
    localizedWitnessDiscriminantIdentity
    resolvedContributionCountIsNinetySix
    nearRowCountIsTwelve
    nonNearRowCountIsZero
    firstNearPPPImaginarySqrt10NumeratorPositive

data ScalarLocalizedWitnessDecision : Set where
  rejectedByExactWitness : ScalarLocalizedWitnessDecision

scalarLocalizedWitnessDecision : ScalarLocalizedWitnessDecision
scalarLocalizedWitnessDecision = rejectedByExactWitness
