module DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- A finite Galerkin state is represented by positive-orbit coefficients with
-- transversality evidence.  The negative mode and coefficient are not supplied
-- independently:
--
--   mode(-)  = - mode(+),
--   value(-) = conjugate(value(+)).
--
-- Reality is therefore built into reconstruction.  Transversality of the
-- reconstructed negative coefficient follows from one explicit conjugation
-- law for the selected real-field instance; it is not hidden in a Boolean
-- status flag.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

record TransverseModeCoefficient
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  constructor transverse-mode-coefficient
  field
    coefficientMode : Z3.FourierMode
    coefficientValue : C3.Complex3 F
    transverse :
      C3.bilinearDot3
        (C3.modeVector E coefficientMode)
        coefficientValue
      ≡ C3.complexZero F

open TransverseModeCoefficient public

reconstructedNegativeMode :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  TransverseModeCoefficient F E → Z3.FourierMode
reconstructedNegativeMode coefficient =
  Z3.negateMode (coefficientMode coefficient)

reconstructedNegativeValue :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  TransverseModeCoefficient F E → C3.Complex3 F
reconstructedNegativeValue coefficient =
  C3.complex3Conjugate (coefficientValue coefficient)

negativeModeIsNegation :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficient : TransverseModeCoefficient F E) →
  reconstructedNegativeMode coefficient
  ≡ Z3.negateMode (coefficientMode coefficient)
negativeModeIsNegation coefficient = refl

negativeValueIsConjugate :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficient : TransverseModeCoefficient F E) →
  reconstructedNegativeValue coefficient
  ≡ C3.complex3Conjugate (coefficientValue coefficient)
negativeValueIsConjugate coefficient = refl

record ConjugateTransversalityLaw
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    conjugatePreservesTransverse :
      ∀ mode value →
      C3.bilinearDot3 (C3.modeVector E mode) value
        ≡ C3.complexZero F →
      C3.bilinearDot3
        (C3.modeVector E (Z3.negateMode mode))
        (C3.complex3Conjugate value)
        ≡ C3.complexZero F

open ConjugateTransversalityLaw public

reconstructedNegativeIsTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  (law : ConjugateTransversalityLaw F E) →
  (coefficient : TransverseModeCoefficient F E) →
  C3.bilinearDot3
    (C3.modeVector E (reconstructedNegativeMode coefficient))
    (reconstructedNegativeValue coefficient)
  ≡ C3.complexZero F
reconstructedNegativeIsTransverse law coefficient =
  conjugatePreservesTransverse law
    (coefficientMode coefficient)
    (coefficientValue coefficient)
    (transverse coefficient)

record LiteralRealGalerkinPhaseSpace
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  constructor literal-real-galerkin-phase-space
  field
    positiveOrbitCoefficients : List (TransverseModeCoefficient F E)

open LiteralRealGalerkinPhaseSpace public

reconstructedModeCount :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  LiteralRealGalerkinPhaseSpace F E → List Z3.FourierMode
reconstructedModeCount phaseSpace =
  appendPositiveNegative (positiveOrbitCoefficients phaseSpace)
  where
  appendPositiveNegative :
    List (TransverseModeCoefficient F E) → List Z3.FourierMode
  appendPositiveNegative [] = []
  appendPositiveNegative (coefficient ∷ rest) =
    coefficientMode coefficient
    ∷ reconstructedNegativeMode coefficient
    ∷ appendPositiveNegative rest
