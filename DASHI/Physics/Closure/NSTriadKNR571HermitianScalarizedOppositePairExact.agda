module DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact where

------------------------------------------------------------------------
-- R571 LOCAL HERMITIAN SCALARIZATION -> EXISTING OPPOSITE R27 PAIR
--
-- G0' is deliberately local.  We do NOT construct a global physical scalar
-- Fourier state.  Given two literal rational C^3 samples X-/X+ and the actual
-- spectator/test vector D, use the already-owned real-Hermitian functional
--
--     phi_D(X) = Re <X,D>
--
-- to obtain the two scalars consumed by the old centered pair.  R27's
-- FourierStateCarrier is only a function FourierMode -> Q, and the opposite
-- pair consumes only its center evaluation, so constant local carriers are
-- sufficient for this adapter and carry no extra physical semantics.
--
-- The main theorem proves that the old scalar weighted raw pair is EXACTLY the
-- real-Hermitian scalarization of the corresponding signed vector pair.  No
-- norm, Cauchy estimate, G1/G2 envelope, fibre sum, or R568 payment enters.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571HomochiralPairedSecondMomentRealizationExact as R571Pair
import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Centered
import DASHI.Physics.Closure.NSTriadKNR571OppositeRound27PairedTaylorExact as Opp

------------------------------------------------------------------------
-- 1. Existing scalar functional and a deliberately local R27 carrier.
------------------------------------------------------------------------

hermitianScalar :
  C3.Complex3 Weld.F → C3.Complex3 Weld.F → ℚ
hermitianScalar X D = R179.realHermitianCross X D

localScalarState : ℚ → R27.FourierStateCarrier
localScalarState value = record
  { R27.stateCoefficient = λ _ → value
  }

localScalarStateAt :
  (value : ℚ) (mode : Z3.FourierMode) →
  R27.stateCoefficient (localScalarState value) mode ≡ value
localScalarStateAt value mode = refl

------------------------------------------------------------------------
-- 2. Signed vector pair and exact Hermitian scalarization.
------------------------------------------------------------------------

signedVectorPair :
  ℚ → ℚ → ℚ →
  C3.Complex3 Weld.F → C3.Complex3 Weld.F →
  C3.Complex3 Weld.F
signedVectorPair aMinus aCenter aPlus XMinus XPlus =
  C3.complex3Add
    (R291.realScale (aMinus - aCenter) XMinus)
    (R291.realScale (aPlus - aCenter) XPlus)

weightedSignedVectorPair :
  ℚ → ℚ → ℚ → ℚ →
  C3.Complex3 Weld.F → C3.Complex3 Weld.F →
  C3.Complex3 Weld.F
weightedSignedVectorPair weight aMinus aCenter aPlus XMinus XPlus =
  R291.realScale weight
    (signedVectorPair aMinus aCenter aPlus XMinus XPlus)

weightedHermitianScalarization :
  (weight aMinus aCenter aPlus : ℚ) →
  (XMinus XPlus D : C3.Complex3 Weld.F) →
  hermitianScalar
    (weightedSignedVectorPair
      weight aMinus aCenter aPlus XMinus XPlus)
    D
  ≡
  weight *
    ( (aMinus - aCenter) * hermitianScalar XMinus D
    + (aPlus - aCenter) * hermitianScalar XPlus D )
weightedHermitianScalarization
    weight aMinus aCenter aPlus XMinus XPlus D =
  let
    outer :
      hermitianScalar
        (weightedSignedVectorPair
          weight aMinus aCenter aPlus XMinus XPlus)
        D
      ≡
      weight * hermitianScalar
        (signedVectorPair aMinus aCenter aPlus XMinus XPlus) D
    outer = R291.scaledRealCrossLeft
      weight
      (signedVectorPair aMinus aCenter aPlus XMinus XPlus)
      D

    add :
      hermitianScalar
        (signedVectorPair aMinus aCenter aPlus XMinus XPlus) D
      ≡
      hermitianScalar (R291.realScale (aMinus - aCenter) XMinus) D
      + hermitianScalar (R291.realScale (aPlus - aCenter) XPlus) D
    add = R291.realCrossAddLeft
      (R291.realScale (aMinus - aCenter) XMinus)
      (R291.realScale (aPlus - aCenter) XPlus)
      D

    left :
      hermitianScalar (R291.realScale (aMinus - aCenter) XMinus) D
      ≡ (aMinus - aCenter) * hermitianScalar XMinus D
    left = R291.scaledRealCrossLeft (aMinus - aCenter) XMinus D

    right :
      hermitianScalar (R291.realScale (aPlus - aCenter) XPlus) D
      ≡ (aPlus - aCenter) * hermitianScalar XPlus D
    right = R291.scaledRealCrossLeft (aPlus - aCenter) XPlus D
  in
  trans outer
    (trans
      (cong (weight *_) add)
      (cong (weight *_) (cong₂ _+_ left right)))

------------------------------------------------------------------------
-- 3. Existing OppositeRound27PairData with Hermitian g-/g+ values.
------------------------------------------------------------------------

hermitianOppositePairData :
  (sign : R311.HelicitySign) →
  (scalars : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode plusShift minusShift : Z3.FourierMode) →
  (XPlus XMinus D : C3.Complex3 Weld.F) →
  (kernelWeight linearModel : ℚ) →
  R27.shiftedMode plusShift plusMode ≡ centerMode →
  R27.shiftedMode minusShift minusMode ≡ centerMode →
  Opp.OppositeRound27PairData
hermitianOppositePairData
    sign scalars centerMode plusMode minusMode plusShift minusShift
    XPlus XMinus D kernelWeight linearModel plusLands minusLands = record
  { Opp.sign = sign
  ; Opp.scalars = scalars
  ; Opp.centerMode = centerMode
  ; Opp.plusMode = plusMode
  ; Opp.minusMode = minusMode
  ; Opp.plusShift = plusShift
  ; Opp.minusShift = minusShift
  ; Opp.plusState = localScalarState (hermitianScalar XPlus D)
  ; Opp.minusState = localScalarState (hermitianScalar XMinus D)
  ; Opp.kernelWeight = kernelWeight
  ; Opp.linearModel = linearModel
  ; Opp.gPlus = hermitianScalar XPlus D
  ; Opp.gMinus = hermitianScalar XMinus D
  ; Opp.plusShiftLandsAtCenter = plusLands
  ; Opp.minusShiftLandsAtCenter = minusLands
  ; Opp.plusStateAtCenter = refl
  ; Opp.minusStateAtCenter = refl
  }

hermitianPairCenterValuesExact :
  (sign : R311.HelicitySign) →
  (scalars : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode plusShift minusShift : Z3.FourierMode) →
  (XPlus XMinus D : C3.Complex3 Weld.F) →
  (kernelWeight linearModel : ℚ) →
  (plusLands : R27.shiftedMode plusShift plusMode ≡ centerMode) →
  (minusLands : R27.shiftedMode minusShift minusMode ≡ centerMode) →
  let dataSet = hermitianOppositePairData
        sign scalars centerMode plusMode minusMode plusShift minusShift
        XPlus XMinus D kernelWeight linearModel plusLands minusLands
  in
  R27.stateCoefficient (Opp.plusState dataSet) centerMode
    ≡ hermitianScalar XPlus D
hermitianPairCenterValuesExact
    sign scalars centerMode plusMode minusMode plusShift minusShift
    XPlus XMinus D kernelWeight linearModel plusLands minusLands = refl

------------------------------------------------------------------------
-- 4. G0': old centered scalar pair = scalarized signed vector pair.
------------------------------------------------------------------------

hermitianScalarizedPairIsCenteredRawPair :
  (sign : R311.HelicitySign) →
  (scalars : Helical.HelicalModeScalars Weld.F) →
  (centerMode plusMode minusMode plusShift minusShift : Z3.FourierMode) →
  (XPlus XMinus D : C3.Complex3 Weld.F) →
  (kernelWeight linearModel : ℚ) →
  (plusLands : R27.shiftedMode plusShift plusMode ≡ centerMode) →
  (minusLands : R27.shiftedMode minusShift minusMode ≡ centerMode) →
  let dataSet = hermitianOppositePairData
        sign scalars centerMode plusMode minusMode plusShift minusShift
        XPlus XMinus D kernelWeight linearModel plusLands minusLands
      sample = Opp.pairedCenteredSample dataSet
  in
  hermitianScalar
    (weightedSignedVectorPair
      kernelWeight
      (Centered.aMinus sample)
      (Centered.aCenter sample)
      (Centered.aPlus sample)
      XMinus XPlus)
    D
  ≡ Centered.weightedRawPair sample
hermitianScalarizedPairIsCenteredRawPair
    sign scalars centerMode plusMode minusMode plusShift minusShift
    XPlus XMinus D kernelWeight linearModel plusLands minusLands =
  weightedHermitianScalarization
    kernelWeight
    (R571Pair.radialSymbol sign scalars minusMode)
    (R571Pair.radialSymbol sign scalars centerMode)
    (R571Pair.radialSymbol sign scalars plusMode)
    XMinus XPlus D

------------------------------------------------------------------------
-- Status: this pays only the local vector->scalar same-object adapter.
------------------------------------------------------------------------

r571HermitianScalarizedOppositePairClosed : Bool
r571HermitianScalarizedOppositePairClosed = true

r571GlobalPhysicalScalarStateRequired : Bool
r571GlobalPhysicalScalarStateRequired = false

r571HermitianScalarizationIntroducesAnalyticEstimate : Bool
r571HermitianScalarizationIntroducesAnalyticEstimate = false

r571HermitianScalarizationClosesStateEnvelope : Bool
r571HermitianScalarizationClosesStateEnvelope = false

r571HermitianScalarizationClosesR568 : Bool
r571HermitianScalarizationClosesR568 = false
