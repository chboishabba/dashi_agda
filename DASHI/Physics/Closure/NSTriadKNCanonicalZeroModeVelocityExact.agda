module DASHI.Physics.Closure.NSTriadKNCanonicalZeroModeVelocityExact where

------------------------------------------------------------------------
-- CANONICAL MEAN-ZERO LOOKUP: THE ZERO FOURIER COEFFICIENT IS LITERALLY ZERO
--
-- A reconstructed physical state stores only nonzero positive representatives.
-- Therefore zeroMode cannot occur in its positive list.  Since -zeroMode is
-- definitionally zeroMode, Round35's executable outside-support theorem then
-- forces the canonical same-object velocity lookup at zeroMode to be the
-- literal Complex3 zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact as Phase
import DASHI.Physics.Closure.NSTriadKNConcreteReconstructedPhysicalSelectorRound29Exact as State
import DASHI.Physics.Closure.NSTriadKNSameObjectLookupConsistencyRound33Exact as Lookup
import DASHI.Physics.Closure.NSTriadKNCanonicalVelocityRealityRound35Exact as Reality

positiveModeOccursZeroIsFalse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (state : State.ReconstructedPhysicalState F E) →
  Lookup.positiveModeOccurs
    (State.positiveOrbitCoefficients state)
    Z3.zeroMode
  ≡ false
positiveModeOccursZeroIsFalse state
  with Lookup.positiveModeOccurs
    (State.positiveOrbitCoefficients state)
    Z3.zeroMode in occurs
... | false = refl
... | true
  with Lookup.positiveModeOccursSound
    {coefficients = State.positiveOrbitCoefficients state}
    {mode = Z3.zeroMode}
    occurs
... | Lookup.positive-mode-hit coefficient member zeroExact =
  ⊥-elim
    (Z3.notZero
      (State.positiveModesNonzero state coefficient member)
      (sym zeroExact))

canonicalZeroModeVelocity :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    {state : State.ReconstructedPhysicalState F E}
    (compatibility : Lookup.SameObjectCompatibleState F E state) →
  Lookup.literalVelocityAt compatibility Z3.zeroMode
  ≡ C3.complex3Zero F
canonicalZeroModeVelocity {state = state} compatibility =
  Reality.literalVelocityZeroIfNeitherPositive
    compatibility
    Z3.zeroMode
    (positiveModeOccursZeroIsFalse state)
    (positiveModeOccursZeroIsFalse state)

canonicalZeroModeVelocityClosed : Bool
canonicalZeroModeVelocityClosed = true

canonicalZeroModeVelocityClosedIsTrue :
  canonicalZeroModeVelocityClosed ≡ true
canonicalZeroModeVelocityClosedIsTrue = refl
