module DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Zhen Lei; Fang-Hua Lin; Yi Zhou.
-- Title: "Structure of Helicity and Global Solutions of Incompressible
-- Navier-Stokes Equation".
-- Venue/year: Archive for Rational Mechanics and Analysis 218 (2015).
-- DOI: 10.1007/s00205-015-0884-8.
-- Uses: the positive/negative curl spectral decomposition and the signed
-- critical-energy identity.
-- Relationship: defines the literal periodic Fourier operators.  The cited
-- theorem is conditional on helical dominance and is not used as a universal
-- coercivity theorem.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3

complex3Cross :
  ∀ {r} {F : C3.RealField r} →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F
complex3Cross a b =
  C3.complex3
    (C3.complexSubtract
      (C3.complexMultiply (C3.y a) (C3.z b))
      (C3.complexMultiply (C3.z a) (C3.y b)))
    (C3.complexSubtract
      (C3.complexMultiply (C3.z a) (C3.x b))
      (C3.complexMultiply (C3.x a) (C3.z b)))
    (C3.complexSubtract
      (C3.complexMultiply (C3.x a) (C3.y b))
      (C3.complexMultiply (C3.y a) (C3.x b)))

curlSymbol :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
curlSymbol {F = F} E k value =
  C3.complex3Scale
    (C3.complexI F)
    (complex3Cross (C3.modeVector E k) value)

Transverse :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → C3.Complex3 F → Set r
Transverse {F = F} E k value =
  C3.bilinearDot3 (C3.modeVector E k) value ≡ C3.complexZero F

record HelicalModeScalars
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  field
    modeNorm inverseModeNorm : Z3.FourierMode → C3.Carrier F
    half : C3.Carrier F

open HelicalModeScalars public

helicalProjectorPlus :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : HelicalModeScalars F) →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
helicalProjectorPlus {F = F} E I S k value =
  C3.complex3Scale (C3.realEmbed F (half S))
    (C3.complex3Add
      (C3.lerayProject3 E I k value)
      (C3.complex3Scale
        (C3.realEmbed F (inverseModeNorm S k))
        (curlSymbol E k value)))

helicalProjectorMinus :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : HelicalModeScalars F) →
  Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
helicalProjectorMinus {F = F} E I S k value =
  C3.complex3Scale (C3.realEmbed F (half S))
    (C3.complex3Subtract
      (C3.lerayProject3 E I k value)
      (C3.complex3Scale
        (C3.realEmbed F (inverseModeNorm S k))
        (curlSymbol E k value)))

helicalProjectorPlusDefinition :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : HelicalModeScalars F)
    (k : Z3.FourierMode) (value : C3.Complex3 F) →
  helicalProjectorPlus E I S k value
  ≡
  C3.complex3Scale (C3.realEmbed F (half S))
    (C3.complex3Add
      (C3.lerayProject3 E I k value)
      (C3.complex3Scale
        (C3.realEmbed F (inverseModeNorm S k))
        (curlSymbol E k value)))
helicalProjectorPlusDefinition E I S k value = refl

helicalProjectorMinusDefinition :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : HelicalModeScalars F)
    (k : Z3.FourierMode) (value : C3.Complex3 F) →
  helicalProjectorMinus E I S k value
  ≡
  C3.complex3Scale (C3.realEmbed F (half S))
    (C3.complex3Subtract
      (C3.lerayProject3 E I k value)
      (C3.complex3Scale
        (C3.realEmbed F (inverseModeNorm S k))
        (curlSymbol E k value)))
helicalProjectorMinusDefinition E I S k value = refl

data HelicitySign : Set where
  plus minus : HelicitySign

helicalProjector :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : HelicalModeScalars F) →
  HelicitySign → Z3.FourierMode → C3.Complex3 F → C3.Complex3 F
helicalProjector E I S plus = helicalProjectorPlus E I S
helicalProjector E I S minus = helicalProjectorMinus E I S

helicityDensity :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  Z3.FourierMode → C3.Complex3 F → C3.Carrier F
helicityDensity E k value =
  C3.real (C3.hermitianPairing3 value (curlSymbol E k value))

mapHelicity :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  (Z3.FourierMode → C3.Complex3 F) →
  List Z3.FourierMode → List (C3.Carrier F)
mapHelicity E velocity [] = []
mapHelicity E velocity (k ∷ modes) =
  helicityDensity E k (velocity k) ∷ mapHelicity E velocity modes

sumScalars :
  ∀ {r} (F : C3.RealField r) →
  List (C3.Carrier F) → C3.Carrier F
sumScalars F [] = C3.zero F
sumScalars F (x ∷ xs) = C3.add F x (sumScalars F xs)

periodicHelicityLiteralFourierSum :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F →
  List Z3.FourierMode →
  (Z3.FourierMode → C3.Complex3 F) →
  C3.Carrier F
periodicHelicityLiteralFourierSum {F = F} E modes velocity =
  sumScalars F (mapHelicity E velocity modes)

record PeriodicHelicalProjectorLaws
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : HelicalModeScalars F) : Set (lsuc r) where
  field
    curlSymbolRealityCompatible :
      ∀ k value →
      curlSymbol E (Z3.negateMode k) (C3.complex3Conjugate value)
      ≡ C3.complex3Conjugate (curlSymbol E k value)

    curlSymbolPreservesTransverse :
      ∀ k value → Transverse E k value →
      Transverse E k (curlSymbol E k value)

    curlSymbolSelfAdjointOnTransverse :
      ∀ k u v → Transverse E k u → Transverse E k v →
      C3.hermitianPairing3 (curlSymbol E k u) v
      ≡ C3.hermitianPairing3 u (curlSymbol E k v)

    curlSymbolSquaredOnTransverse :
      ∀ k value → Transverse E k value →
      curlSymbol E k (curlSymbol E k value)
      ≡ C3.complex3Scale
          (C3.realEmbed F (C3.normSquared I k))
          value

    helicalProjectorIdempotent :
      ∀ sign k value →
      helicalProjector E I S sign k
        (helicalProjector E I S sign k value)
      ≡ helicalProjector E I S sign k value

    helicalProjectorSelfAdjoint :
      ∀ sign k u v →
      C3.hermitianPairing3 (helicalProjector E I S sign k u) v
      ≡ C3.hermitianPairing3 u (helicalProjector E I S sign k v)

    helicalProjectorsOrthogonal :
      ∀ k u v →
      C3.hermitianPairing3
        (helicalProjectorPlus E I S k u)
        (helicalProjectorMinus E I S k v)
      ≡ C3.complexZero F

    helicalProjectorsSumToLeray :
      ∀ k value →
      C3.complex3Add
        (helicalProjectorPlus E I S k value)
        (helicalProjectorMinus E I S k value)
      ≡ C3.lerayProject3 E I k value

    helicalProjectorRealityCompatible :
      ∀ sign k value →
      helicalProjector E I S sign (Z3.negateMode k)
        (C3.complex3Conjugate value)
      ≡ C3.complex3Conjugate
          (helicalProjector E I S sign k value)

    helicalProjectorDivergenceFree :
      ∀ sign k value →
      Transverse E k (helicalProjector E I S sign k value)

    helicalCurlEigenvaluePlus :
      ∀ k value →
      curlSymbol E k (helicalProjectorPlus E I S k value)
      ≡ C3.complex3Scale
          (C3.realEmbed F (modeNorm S k))
          (helicalProjectorPlus E I S k value)

    helicalCurlEigenvalueMinus :
      ∀ k value →
      curlSymbol E k (helicalProjectorMinus E I S k value)
      ≡ C3.complex3Scale
          (C3.realEmbed F (C3.negate F (modeNorm S k)))
          (helicalProjectorMinus E I S k value)

    velocityHelicalDecomposition :
      ∀ k value → Transverse E k value →
      C3.complex3Add
        (helicalProjectorPlus E I S k value)
        (helicalProjectorMinus E I S k value)
      ≡ value

    helicalComponentsStronglyOrthogonal :
      ∀ k value →
      C3.hermitianPairing3
        (helicalProjectorPlus E I S k value)
        (helicalProjectorMinus E I S k value)
      ≡ C3.complexZero F

    squaredNorm hsSquaredNorm :
      Z3.FourierMode → C3.Complex3 F → C3.Carrier F

    helicalL2Pythagoras :
      ∀ k value →
      squaredNorm k value
      ≡ C3.add F
          (squaredNorm k (helicalProjectorPlus E I S k value))
          (squaredNorm k (helicalProjectorMinus E I S k value))

    helicalHsPythagoras :
      ∀ k value →
      hsSquaredNorm k value
      ≡ C3.add F
          (hsSquaredNorm k (helicalProjectorPlus E I S k value))
          (hsSquaredNorm k (helicalProjectorMinus E I S k value))

    helicityEqualsSignedHalfSobolevDifference :
      ∀ k value →
      helicityDensity E k value
      ≡ C3.add F
          (hsSquaredNorm k (helicalProjectorPlus E I S k value))
          (C3.negate F
            (hsSquaredNorm k (helicalProjectorMinus E I S k value)))

    EulerNonlinearDerivative NavierStokesHelicityDerivative
      HelicityDissipationDifference :
      Z3.FourierMode → C3.Complex3 F → C3.Carrier F

    helicityEulerNonlinearDerivativeVanishes :
      ∀ k value →
      EulerNonlinearDerivative k value ≡ C3.zero F

    helicityNavierStokesDerivativeIdentity :
      ∀ k value →
      NavierStokesHelicityDerivative k value
      ≡ HelicityDissipationDifference k value

    helicalCriticalEnergyDifferenceIdentity :
      ∀ k value →
      helicityDensity E k value
      ≡ C3.add F
          (hsSquaredNorm k (helicalProjectorPlus E I S k value))
          (C3.negate F
            (hsSquaredNorm k (helicalProjectorMinus E I S k value)))

open PeriodicHelicalProjectorLaws public

periodicHelicalInfrastructureRepresented : Bool
periodicHelicalInfrastructureRepresented = true

periodicHelicalInfrastructureRepresentedIsTrue :
  periodicHelicalInfrastructureRepresented ≡ true
periodicHelicalInfrastructureRepresentedIsTrue = refl

periodicHelicalAnalyticLawsClosed : Bool
periodicHelicalAnalyticLawsClosed = false

periodicHelicalAnalyticLawsClosedIsFalse :
  periodicHelicalAnalyticLawsClosed ≡ false
periodicHelicalAnalyticLawsClosedIsFalse = refl
