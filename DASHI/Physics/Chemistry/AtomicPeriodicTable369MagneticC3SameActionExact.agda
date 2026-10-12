module DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3SameActionExact where

------------------------------------------------------------------------
-- SAME-ACTION RECOGNITION
--
-- The p-shell realization owner already pays:
--   ternary depth-one carrier -> magnetic triplet -> existing C3 residue,
-- together with an exact ternary/physical commuting square.
--
-- This owner proves that the step on both sides is not merely graph-isomorphic:
-- after the same-object residue maps it is literally the repository's existing
-- +1 translation in Z/3Z.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Data.Vec using ([]; _∷_)

import DASHI.Biology.TriadicKernelLiftQuotientExact as Triadic
import DASHI.Foundations.TriadicFiniteQuotient as Quotient
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3

translatePositive :
  Quotient.Residue3Pow Quotient.one -> Quotient.Residue3Pow Quotient.one
translatePositive residue = Arithmetic.addResidue residue Characters.rPos

translatePositiveOrderThree :
  (r : Quotient.Residue3Pow Quotient.one) ->
  translatePositive (translatePositive (translatePositive r)) ≡ r
translatePositiveOrderThree (Triadic.negativeTrit ∷ []) = refl
translatePositiveOrderThree (Triadic.zeroTrit ∷ []) = refl
translatePositiveOrderThree (Triadic.positiveTrit ∷ []) = refl

ternaryStepIsPositiveTranslation :
  (x : C3.DepthOneKernel) ->
  C3.kernelResidue (C3.ternaryChargePositiveStep x)
  ≡ translatePositive (C3.kernelResidue x)
ternaryStepIsPositiveTranslation (Triadic.negativeTrit ∷ []) = refl
ternaryStepIsPositiveTranslation (Triadic.zeroTrit ∷ []) = refl
ternaryStepIsPositiveTranslation (Triadic.positiveTrit ∷ []) = refl

physicalStepIsPositiveTranslation :
  (m : C3.MagneticState) ->
  C3.sectorResidue (C3.magneticSector (C3.chargePositiveStep m))
  ≡ translatePositive (C3.sectorResidue (C3.magneticSector m))
physicalStepIsPositiveTranslation C3.mNegOne = refl
physicalStepIsPositiveTranslation C3.mZero = refl
physicalStepIsPositiveTranslation C3.mPosOne = refl

sameActionRecognitionSquare :
  (x : C3.DepthOneKernel) ->
  C3.sectorResidue
    (C3.magneticSector
      (C3.realizeMagneticState (C3.ternaryChargePositiveStep x)))
  ≡ translatePositive (C3.kernelResidue x)
sameActionRecognitionSquare (Triadic.negativeTrit ∷ []) = refl
sameActionRecognitionSquare (Triadic.zeroTrit ∷ []) = refl
sameActionRecognitionSquare (Triadic.positiveTrit ∷ []) = refl

sameActionOnRealizedState :
  (x : C3.DepthOneKernel) ->
  C3.sectorResidue
    (C3.magneticSector
      (C3.chargePositiveStep (C3.realizeMagneticState x)))
  ≡ translatePositive (C3.kernelResidue x)
sameActionOnRealizedState (Triadic.negativeTrit ∷ []) = refl
sameActionOnRealizedState (Triadic.zeroTrit ∷ []) = refl
sameActionOnRealizedState (Triadic.positiveTrit ∷ []) = refl

record MagneticC3SameActionBoundary : Set where
  constructor magneticC3SameActionBoundary
  field
    ternaryStepRecognizedAsExistingC3Translation : Bool
    physicalStepRecognizedAsExistingC3Translation : Bool
    sameActionSquarePaid : Bool
    graphSimilarityUsedAsProof : Bool
    interactingHamiltonianActionRecognized : Bool

canonicalMagneticC3SameActionBoundary : MagneticC3SameActionBoundary
canonicalMagneticC3SameActionBoundary =
  magneticC3SameActionBoundary true true true false false

graphSimilarityUsedAsProofIsFalse :
  MagneticC3SameActionBoundary.graphSimilarityUsedAsProof
    canonicalMagneticC3SameActionBoundary
  ≡ false
graphSimilarityUsedAsProofIsFalse = refl

interactingHamiltonianActionRecognizedIsFalse :
  MagneticC3SameActionBoundary.interactingHamiltonianActionRecognized
    canonicalMagneticC3SameActionBoundary
  ≡ false
interactingHamiltonianActionRecognizedIsFalse = refl
