module DASHI.Physics.Chemistry.AtomicPeriodicTable369C3FourierSpatialRestrictionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)

import DASHI.Algebra.TriadicDepthOneCharacters as Characters
import DASHI.Algebra.TriadicFiniteArithmetic as Arithmetic
import DASHI.Foundations.TriadicFiniteQuotient as Quotient
import DASHI.Physics.Chemistry.AtomicPeriodicTable369MagneticC3PhysicalRealizationExact as C3

------------------------------------------------------------------------
-- Purpose
--
-- The atomic p-shell owner has two order-three actions on the same three-state
-- carrier:
--
--   * chargePositiveStep : a cyclic permutation of magnetic/residue sectors;
--   * rotationPhase      : the diagonal C3 character of a 120-degree spatial
--                          z rotation in the complex magnetic basis.
--
-- They are NOT the same operator in one basis.  The exact relationship is the
-- ordinary finite Fourier decomposition of the regular representation of C3:
-- characters diagonalize translation.  This module pays that statement in the
-- repository's existing symbolic phase ring, without manufacturing complex
-- amplitudes or an analytic spatial wavefunction.
------------------------------------------------------------------------

frequencyOfMagneticState :
  C3.MagneticState -> Quotient.Residue3Pow Quotient.one
frequencyOfMagneticState C3.mNegOne = Characters.rNeg
frequencyOfMagneticState C3.mZero = Characters.rZero
frequencyOfMagneticState C3.mPosOne = Characters.rPos

fourierCharacter :
  C3.MagneticState ->
  Quotient.Residue3Pow Quotient.one ->
  Characters.C3Phase
fourierCharacter m x = Characters.characterValue (frequencyOfMagneticState m) x

positiveTranslationMultiplier : C3.MagneticState -> Characters.C3Phase
positiveTranslationMultiplier m =
  Characters.characterValue (frequencyOfMagneticState m) Characters.rPos

positiveTranslationMultiplierIsSpatialRotationPhase :
  (m : C3.MagneticState) ->
  positiveTranslationMultiplier m ≡ C3.rotationPhase m
positiveTranslationMultiplierIsSpatialRotationPhase C3.mNegOne = refl
positiveTranslationMultiplierIsSpatialRotationPhase C3.mZero = refl
positiveTranslationMultiplierIsSpatialRotationPhase C3.mPosOne = refl

fourierCharacterDiagonalizesPositiveTranslation :
  (m : C3.MagneticState)
  (x : Quotient.Residue3Pow Quotient.one) ->
  fourierCharacter m (Arithmetic.addResidue x Characters.rPos)
  ≡
  Characters.multiplyPhase
    (fourierCharacter m x)
    (C3.rotationPhase m)
fourierCharacterDiagonalizesPositiveTranslation m x =
  trans
    (Characters.characterAdditive
      (frequencyOfMagneticState m)
      x
      Characters.rPos)
    (cong
      (Characters.multiplyPhase (fourierCharacter m x))
      (positiveTranslationMultiplierIsSpatialRotationPhase m))

------------------------------------------------------------------------
-- Representation-level boundary.
------------------------------------------------------------------------

record C3FourierSpatialRestrictionBoundary : Set where
  constructor c3FourierSpatialRestrictionBoundary
  field
    chargeTranslationRegularRepresentationPaid : Bool
    spatialRotationCharacterRepresentationPaid : Bool
    exactFourierCharacterDiagonalizationPaid : Bool
    sameRepresentationUpToFourierBasisPaid : Bool

    sameMatrixInMagneticBasis : Bool
    analyticUnitaryDFTMatrixPaidInAgda : Bool
    fullSO3RepresentationPaidHere : Bool
    physicalChargeTransportIdentifiedWithSpatialRotationMechanism : Bool

open C3FourierSpatialRestrictionBoundary public

canonicalC3FourierSpatialRestrictionBoundary : C3FourierSpatialRestrictionBoundary
canonicalC3FourierSpatialRestrictionBoundary =
  c3FourierSpatialRestrictionBoundary
    true true true true
    false false false false

sameMatrixInMagneticBasisIsFalse :
  sameMatrixInMagneticBasis canonicalC3FourierSpatialRestrictionBoundary ≡ false
sameMatrixInMagneticBasisIsFalse = refl

physicalMechanismIdentificationIsFalse :
  physicalChargeTransportIdentifiedWithSpatialRotationMechanism
    canonicalC3FourierSpatialRestrictionBoundary
  ≡ false
physicalMechanismIdentificationIsFalse = refl
