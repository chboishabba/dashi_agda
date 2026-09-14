module DASHI.Physics.Closure.NSTriadKNR571OppositeRound27PairedTaylorExact where

------------------------------------------------------------------------
-- PUBLICATION CORRECTION: PAIR THE TWO ROUND27 LEGS BEFORE CENTERING
--
-- One Round27 commutator coefficient is one translated multiplier-difference
-- leg.  The old centered commutator carrier is the sum of the +y and -y legs.
-- This owner performs exactly that missing same-object pairing.
--
-- No magnitude estimate, Taylor envelope, six-three gain, fibre sum, R568
-- budget or Clay promotion is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _*_; _-_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNLuoFiniteDyadicMultiplierTaylorDifferenceExact as Taylor
import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Centered
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld

record OppositeRound27PairData : Set₁ where
  field
    sign : R311.HelicitySign
    scalars : Helical.HelicalModeScalars Weld.F

    centerMode plusMode minusMode : Z3.FourierMode
    plusShift minusShift : Z3.FourierMode
    plusState minusState : R27.FourierStateCarrier

    kernelWeight linearModel gPlus gMinus : ℚ

    plusShiftLandsAtCenter :
      R27.shiftedMode plusShift plusMode ≡ centerMode
    minusShiftLandsAtCenter :
      R27.shiftedMode minusShift minusMode ≡ centerMode

    plusStateAtCenter :
      R27.stateCoefficient plusState centerMode ≡ gPlus
    minusStateAtCenter :
      R27.stateCoefficient minusState centerMode ≡ gMinus

open OppositeRound27PairData public

pairedTaylor : OppositeRound27PairData → Taylor.MultiplierTaylorPair
pairedTaylor dataSet =
  R.radialTaylorPair
    (sign dataSet)
    (scalars dataSet)
    (centerMode dataSet)
    (plusMode dataSet)
    (minusMode dataSet)
    (linearModel dataSet)

pairedCenteredSample :
  OppositeRound27PairData → Centered.PairedCommutatorSample
pairedCenteredSample dataSet =
  Centered.paired-commutator-sample
    (kernelWeight dataSet)
    (R.radialSymbol (sign dataSet) (scalars dataSet) (minusMode dataSet))
    (R.radialSymbol (sign dataSet) (scalars dataSet) (centerMode dataSet))
    (R.radialSymbol (sign dataSet) (scalars dataSet) (plusMode dataSet))
    (gMinus dataSet)
    (gPlus dataSet)

pairedCenterIsTaylorCenter :
  (dataSet : OppositeRound27PairData) →
  Centered.aCenter (pairedCenteredSample dataSet)
  ≡ Taylor.center (pairedTaylor dataSet)
pairedCenterIsTaylorCenter dataSet = refl

pairedPlusIsTaylorPlus :
  (dataSet : OppositeRound27PairData) →
  Centered.aPlus (pairedCenteredSample dataSet)
  ≡ Taylor.plusValue (pairedTaylor dataSet)
pairedPlusIsTaylorPlus dataSet =
  R.radialTaylorPlusValueExact
    (sign dataSet)
    (scalars dataSet)
    (centerMode dataSet)
    (plusMode dataSet)
    (minusMode dataSet)
    (linearModel dataSet)
    |> sym
  where
    open import Relation.Binary.PropositionalEquality using (sym)
    infixl 0 _|>_
    _|>_ : ∀ {a b : Set} → a → (a → b) → b
    x |> f = f x

pairedMinusIsTaylorMinus :
  (dataSet : OppositeRound27PairData) →
  Centered.aMinus (pairedCenteredSample dataSet)
  ≡ Taylor.minusValue (pairedTaylor dataSet)
pairedMinusIsTaylorMinus dataSet =
  R.radialTaylorMinusValueExact
    (sign dataSet)
    (scalars dataSet)
    (centerMode dataSet)
    (plusMode dataSet)
    (minusMode dataSet)
    (linearModel dataSet)
    |> sym
  where
    open import Relation.Binary.PropositionalEquality using (sym)
    infixl 0 _|>_
    _|>_ : ∀ {a b : Set} → a → (a → b) → b
    x |> f = f x

pairedRound27Scalar : OppositeRound27PairData → ℚ
pairedRound27Scalar dataSet =
  kernelWeight dataSet
  * ( R.r571Round27Scalar
        (sign dataSet) (scalars dataSet)
        (minusShift dataSet) (minusState dataSet) (minusMode dataSet)
    + R.r571Round27Scalar
        (sign dataSet) (scalars dataSet)
        (plusShift dataSet) (plusState dataSet) (plusMode dataSet)
    )

oppositeRound27PairIsCenteredRawPair :
  (dataSet : OppositeRound27PairData) →
  pairedRound27Scalar dataSet
  ≡ Centered.weightedRawPair (pairedCenteredSample dataSet)
oppositeRound27PairIsCenteredRawPair dataSet
  rewrite plusShiftLandsAtCenter dataSet
        | minusShiftLandsAtCenter dataSet
        | plusStateAtCenter dataSet
        | minusStateAtCenter dataSet =
  solve
    ( kernelWeight dataSet
    ∷ R.radialSymbol (sign dataSet) (scalars dataSet) (centerMode dataSet)
    ∷ R.radialSymbol (sign dataSet) (scalars dataSet) (plusMode dataSet)
    ∷ R.radialSymbol (sign dataSet) (scalars dataSet) (minusMode dataSet)
    ∷ gPlus dataSet
    ∷ gMinus dataSet
    ∷ [])

oppositeRound27PairCenteredIdentity :
  (dataSet : OppositeRound27PairData) →
  pairedRound27Scalar dataSet
  ≡ Centered.weightedCenteredBranch (pairedCenteredSample dataSet)
    + Centered.weightedHighDifferenceBranch (pairedCenteredSample dataSet)
oppositeRound27PairCenteredIdentity dataSet =
  let
    open import Relation.Binary.PropositionalEquality using (trans)
  in
  trans
    (oppositeRound27PairIsCenteredRawPair dataSet)
    (Centered.weightedPairedCommutatorIdentity (pairedCenteredSample dataSet))

r571OppositeRound27PairCarrierClosed : Bool
r571OppositeRound27PairCarrierClosed = true

r571OppositeRound27PairIntroducesEnvelopeEstimate : Bool
r571OppositeRound27PairIntroducesEnvelopeEstimate = false

r571OppositeRound27PairClosesR568 : Bool
r571OppositeRound27PairClosesR568 = false

r571OppositeRound27PairCarrierClosedIsTrue :
  r571OppositeRound27PairCarrierClosed ≡ true
r571OppositeRound27PairCarrierClosedIsTrue = refl
