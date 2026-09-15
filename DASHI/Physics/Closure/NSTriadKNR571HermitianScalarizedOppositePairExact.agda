module DASHI.Physics.Closure.NSTriadKNR571HermitianScalarizedOppositePairExact where

------------------------------------------------------------------------
-- R571 / LIVE VECTOR PAIR -> EXISTING ROUND27 SCALAR CENTERED PAIR
--
-- The Round27 FourierStateCarrier is intentionally weak: it is only a map
-- FourierMode -> Q.  The opposite-pair consumer uses only the value at the
-- consumed center mode.  Therefore no global physical scalar Fourier state is
-- required here.
--
-- Fix the actual spectator/test cell D and scalarize the two live vector
-- samples X-/X+ by the already-used real Hermitian functional
--
--   phi_D(X) = Re <X,D>.
--
-- We then realize those two scalars by constant Round27 carriers and construct
-- the existing OppositeRound27PairData.  The center-value receipts are
-- definitional.  R291 supplies the exact add/real-scale linearity needed to
-- transport signed vector combinations through this scalarization.
--
-- No norm, Cauchy estimate, Taylor envelope, six-three estimate, fibre sum,
-- spacetime budget, or R568 closure is introduced.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _+_; _*_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNR571OppositeRound27PairedTaylorExact as Pair
import DASHI.Physics.Closure.NSTriadKNRawCurlFibreGramRound179Exact as R179
import DASHI.Physics.Closure.NSTriadKNPhysicalGramPairTangentRound291Exact as R291

F : C3.RealField _
F = R291.F

hermitianScalar : C3.Complex3 F → C3.Complex3 F → ℚ
hermitianScalar vector spectator = R179.realHermitianCross vector spectator

constantScalarState : ℚ → R27.FourierStateCarrier
constantScalarState value = R27.fourier-state-carrier (λ _ → value)

record HermitianOppositePairInputs : Set₁ where
  field
    sign : R311.HelicitySign
    scalars : Helical.HelicalModeScalars Weld.F
    centerMode plusMode minusMode : Z3.FourierMode
    plusShift minusShift : Z3.FourierMode
    kernelWeight linearModel : ℚ
    plusVector minusVector spectator : C3.Complex3 F
    plusShiftLandsAtCenter :
      R27.shiftedMode plusShift plusMode ≡ centerMode
    minusShiftLandsAtCenter :
      R27.shiftedMode minusShift minusMode ≡ centerMode

open HermitianOppositePairInputs public

gPlus : HermitianOppositePairInputs → ℚ
gPlus dataSet = hermitianScalar (plusVector dataSet) (spectator dataSet)

gMinus : HermitianOppositePairInputs → ℚ
gMinus dataSet = hermitianScalar (minusVector dataSet) (spectator dataSet)

plusState : HermitianOppositePairInputs → R27.FourierStateCarrier
plusState dataSet = constantScalarState (gPlus dataSet)

minusState : HermitianOppositePairInputs → R27.FourierStateCarrier
minusState dataSet = constantScalarState (gMinus dataSet)

plusStateAtCenter :
  (dataSet : HermitianOppositePairInputs) →
  R27.stateCoefficient (plusState dataSet) (centerMode dataSet)
  ≡ gPlus dataSet
plusStateAtCenter dataSet = refl

minusStateAtCenter :
  (dataSet : HermitianOppositePairInputs) →
  R27.stateCoefficient (minusState dataSet) (centerMode dataSet)
  ≡ gMinus dataSet
minusStateAtCenter dataSet = refl

asOppositeRound27PairData :
  HermitianOppositePairInputs → Pair.OppositeRound27PairData
asOppositeRound27PairData dataSet = record
  { sign = sign dataSet
  ; scalars = scalars dataSet
  ; centerMode = centerMode dataSet
  ; plusMode = plusMode dataSet
  ; minusMode = minusMode dataSet
  ; plusShift = plusShift dataSet
  ; minusShift = minusShift dataSet
  ; plusState = plusState dataSet
  ; minusState = minusState dataSet
  ; kernelWeight = kernelWeight dataSet
  ; linearModel = linearModel dataSet
  ; gPlus = gPlus dataSet
  ; gMinus = gMinus dataSet
  ; plusShiftLandsAtCenter = plusShiftLandsAtCenter dataSet
  ; minusShiftLandsAtCenter = minusShiftLandsAtCenter dataSet
  ; plusStateAtCenter = plusStateAtCenter dataSet
  ; minusStateAtCenter = minusStateAtCenter dataSet
  }

hermitianScalarizedPairCenteredIdentity :
  (dataSet : HermitianOppositePairInputs) →
  Pair.pairedRound27Scalar (asOppositeRound27PairData dataSet)
  ≡
  Pair.Centered.weightedCenteredBranch
    (Pair.pairedCenteredSample (asOppositeRound27PairData dataSet))
  +
  Pair.Centered.weightedHighDifferenceBranch
    (Pair.pairedCenteredSample (asOppositeRound27PairData dataSet))
hermitianScalarizedPairCenteredIdentity dataSet =
  Pair.oppositeRound27PairCenteredIdentity
    (asOppositeRound27PairData dataSet)

scalarizesVectorSum :
  (left right spectatorCell : C3.Complex3 F) →
  hermitianScalar (C3.complex3Add left right) spectatorCell
  ≡ hermitianScalar left spectatorCell + hermitianScalar right spectatorCell
scalarizesVectorSum = R291.realCrossAddLeft

scalarizesRealScale :
  (scalar : ℚ) (vector spectatorCell : C3.Complex3 F) →
  hermitianScalar (R291.realScale scalar vector) spectatorCell
  ≡ scalar * hermitianScalar vector spectatorCell
scalarizesRealScale = R291.scaledRealCrossLeft

hermitianOppositePairCarrierClosed : Bool
hermitianOppositePairCarrierClosed = true

hermitianOppositePairCenteredIdentityClosed : Bool
hermitianOppositePairCenteredIdentityClosed = true

hermitianOppositePairIntroducesGlobalScalarState : Bool
hermitianOppositePairIntroducesGlobalScalarState = false

hermitianOppositePairIntroducesEnvelopeEstimate : Bool
hermitianOppositePairIntroducesEnvelopeEstimate = false

hermitianOppositePairClosesR568 : Bool
hermitianOppositePairClosesR568 = false

hermitianOppositePairCarrierClosedIsTrue :
  hermitianOppositePairCarrierClosed ≡ true
hermitianOppositePairCarrierClosedIsTrue = refl

hermitianOppositePairCenteredIdentityClosedIsTrue :
  hermitianOppositePairCenteredIdentityClosed ≡ true
hermitianOppositePairCenteredIdentityClosedIsTrue = refl
