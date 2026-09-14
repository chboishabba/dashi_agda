module DASHI.Physics.Closure.NSTriadKNR571OppositeShiftPairedCommutatorExact where

------------------------------------------------------------------------
-- EXACT TWO-SHIFT CENTERED REALIZATION ON THE R571/R27 RADIAL CARRIER
--
-- At a fixed center mode k and displacement y, Round27 gives
--
--   [M,T_y]u(k)   = (m(k)-m(k-y)) u(k-y),
--   [M,T_-y]u(k)  = (m(k)-m(k+y)) u(k+y).
--
-- Therefore, before absolute values,
--
--  -w ([M,T_y]u(k) + [M,T_-y]u(k))
--   = w ((m(k-y)-m(k))u(k-y) + (m(k+y)-m(k))u(k+y)),
--
-- exactly the old centered PairedCommutatorSample raw scalar.
--
-- The multiplier is the literal signed radial multiplier already welded to
-- R571.  No magnitude, Taylor-envelope, six-three, cutoff, spacetime or PDE
-- estimate is introduced here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; _+_; _-_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNIntegerFourierModeAddExact as Add
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadSymmetry as Sym
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNFiniteTranslationMultiplierCommutatorRound27Exact as R27
import DASHI.Physics.Closure.NSTriadKNNestedInnerHelicityRouteSplitRound311Exact as R311
import DASHI.Physics.Closure.NSTriadKNR571HomochiralRadialIncrementSpecializationExact as Weld
import DASHI.Physics.Closure.NSTriadKNLuoCenteredPairedCommutatorIdentityExact as Centered

plusMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
plusMode center displacement = Z3.addMode center displacement

minusMode : Z3.FourierMode → Z3.FourierMode → Z3.FourierMode
minusMode center displacement =
  Z3.addMode center (Z3.negateMode displacement)

shiftedPlusAtCenterIsMinusMode :
  (center displacement : Z3.FourierMode) →
  R27.shiftedMode displacement center ≡ minusMode center displacement
shiftedPlusAtCenterIsMinusMode center displacement = refl

shiftedMinusAtCenterIsPlusMode :
  (center displacement : Z3.FourierMode) →
  R27.shiftedMode (Z3.negateMode displacement) center
  ≡ plusMode center displacement
shiftedMinusAtCenterIsPlusMode center displacement
  rewrite Sym.negateModeInvolutive displacement = refl

radialSymbol :
  R311.HelicitySign →
  Helical.HelicalModeScalars Weld.F →
  Z3.FourierMode → ℚ
radialSymbol sign S mode =
  R27.multiplierSymbol (Weld.radialMultiplier sign S) mode

positiveShiftCommAtCenter :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  R27.stateCoefficient
    (R27.translationMultiplierCommutator
      (Weld.radialMultiplier sign S) displacement state)
    center
  ≡
  (radialSymbol sign S center
    - radialSymbol sign S (minusMode center displacement))
  * R27.stateCoefficient state (minusMode center displacement)
positiveShiftCommAtCenter sign S displacement state center
  rewrite R27.translationMultiplierCommutatorExact
    (Weld.radialMultiplier sign S) displacement state center
        | shiftedPlusAtCenterIsMinusMode center displacement = refl

negativeShiftCommAtCenter :
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  R27.stateCoefficient
    (R27.translationMultiplierCommutator
      (Weld.radialMultiplier sign S)
      (Z3.negateMode displacement) state)
    center
  ≡
  (radialSymbol sign S center
    - radialSymbol sign S (plusMode center displacement))
  * R27.stateCoefficient state (plusMode center displacement)
negativeShiftCommAtCenter sign S displacement state center
  rewrite R27.translationMultiplierCommutatorExact
    (Weld.radialMultiplier sign S) (Z3.negateMode displacement) state center
        | shiftedMinusAtCenterIsPlusMode center displacement = refl

oppositeShiftPairedSample :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  Centered.PairedCommutatorSample
oppositeShiftPairedSample weight sign S displacement state center =
  Centered.paired-commutator-sample
    weight
    (radialSymbol sign S (minusMode center displacement))
    (radialSymbol sign S center)
    (radialSymbol sign S (plusMode center displacement))
    (R27.stateCoefficient state (minusMode center displacement))
    (R27.stateCoefficient state (plusMode center displacement))

oppositeShiftRound27Scalar :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) → ℚ
oppositeShiftRound27Scalar weight sign S displacement state center =
  weight *
    (-
      ( R27.stateCoefficient
          (R27.translationMultiplierCommutator
            (Weld.radialMultiplier sign S) displacement state)
          center
      + R27.stateCoefficient
          (R27.translationMultiplierCommutator
            (Weld.radialMultiplier sign S)
            (Z3.negateMode displacement) state)
          center
      ))

oppositeShiftRound27ScalarIsWeightedRawPair :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  oppositeShiftRound27Scalar weight sign S displacement state center
  ≡ Centered.weightedRawPair
      (oppositeShiftPairedSample weight sign S displacement state center)
oppositeShiftRound27ScalarIsWeightedRawPair
  weight sign S displacement state center
  rewrite positiveShiftCommAtCenter sign S displacement state center
        | negativeShiftCommAtCenter sign S displacement state center =
  solve
    ( weight
    ∷ radialSymbol sign S center
    ∷ radialSymbol sign S (minusMode center displacement)
    ∷ radialSymbol sign S (plusMode center displacement)
    ∷ R27.stateCoefficient state (minusMode center displacement)
    ∷ R27.stateCoefficient state (plusMode center displacement)
    ∷ [])

oppositeShiftCenteredIdentity :
  (weight : ℚ) →
  (sign : R311.HelicitySign) →
  (S : Helical.HelicalModeScalars Weld.F) →
  (displacement : Z3.FourierMode) →
  (state : R27.FourierStateCarrier) →
  (center : Z3.FourierMode) →
  oppositeShiftRound27Scalar weight sign S displacement state center
  ≡
  Centered.weightedCenteredBranch
    (oppositeShiftPairedSample weight sign S displacement state center)
  + Centered.weightedHighDifferenceBranch
    (oppositeShiftPairedSample weight sign S displacement state center)
oppositeShiftCenteredIdentity weight sign S displacement state center =
  trans
    (oppositeShiftRound27ScalarIsWeightedRawPair
      weight sign S displacement state center)
    (Centered.weightedPairedCommutatorIdentity
      (oppositeShiftPairedSample weight sign S displacement state center))

r571OppositeShiftGeometryClosed : Bool
r571OppositeShiftGeometryClosed = true

r571OppositeShiftPairedRawScalarIdentityClosed : Bool
r571OppositeShiftPairedRawScalarIdentityClosed = true

r571OppositeShiftIntroducesEnvelopeEstimate : Bool
r571OppositeShiftIntroducesEnvelopeEstimate = false

r571OppositeShiftClosesR568 : Bool
r571OppositeShiftClosesR568 = false
