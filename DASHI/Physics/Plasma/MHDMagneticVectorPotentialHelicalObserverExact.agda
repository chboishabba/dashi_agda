module DASHI.Physics.Plasma.MHDMagneticVectorPotentialHelicalObserverExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Level)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNLerayOutputTransversalityRound30Exact as LerayOut
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as Normalized

------------------------------------------------------------------------
-- MAGNETIC VECTOR POTENTIAL ON THE EXACT PERIODIC FOURIER C3 CARRIER
--
-- For a transverse magnetic mode B_k, curl^{-1} is represented as
--
--   A_k = |k|^{-1} ( |k|^{-1} curl_k B_k ).
--
-- The inner normalized curl is already owned by Round142.  The additional
-- inverse-radius factor is the one required by magnetic helicity rather than
-- kinetic helicity.  No gauge statement beyond the periodic transverse
-- Fourier representative is imported here.
------------------------------------------------------------------------

record ModeRadiusCalibration
    {r : Level}
    {F : C3.RealField r}
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) : Set r where
  constructor mode-radius-calibration
  field
    radiusInverse :
      C3.multiply F
        (Helical.modeNorm S k)
        (Helical.inverseModeNorm S k)
      ≡ C3.one F

open ModeRadiusCalibration public

magneticVectorPotentialMode :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex3 F
magneticVectorPotentialMode {F = F} E S k magnetic =
  C3.complex3Scale
    (C3.realEmbed F (Helical.inverseModeNorm S k))
    (Normalized.normalizedCurl E S k magnetic)

magneticHelicityMode :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) →
  C3.Complex3 F → C3.Complex F
magneticHelicityMode E S k magnetic =
  C3.complexRealPart
    (C3.hermitianPairing3 magnetic
      (magneticVectorPotentialMode E S k magnetic))

------------------------------------------------------------------------
-- Lift r * r^{-1} = 1 from the real carrier to nested complex-vector scale.
------------------------------------------------------------------------

embeddedRadiusInverse :
  ∀ {r} {F : C3.RealField r}
    (radius inverse : C3.Carrier F) →
  C3.multiply F radius inverse ≡ C3.one F →
  C3.complexMultiply
    (C3.realEmbed F inverse)
    (C3.realEmbed F radius)
  ≡ C3.complexOne F
embeddedRadiusInverse {F = F} radius inverse inverseLaw =
  trans
    (Field.complexMultiplyCommutative
      (C3.realEmbed F inverse) (C3.realEmbed F radius))
    (trans
      (LerayOut.realEmbedMultiply radius inverse)
      (cong (C3.realEmbed F) inverseLaw))

nestedInverseRadiusScaleCancels :
  ∀ {r} {F : C3.RealField r}
    (radius inverse : C3.Carrier F) →
  C3.multiply F radius inverse ≡ C3.one F →
  (value : C3.Complex3 F) →
  C3.complex3Scale (C3.realEmbed F inverse)
    (C3.complex3Scale (C3.realEmbed F radius) value)
  ≡ value
nestedInverseRadiusScaleCancels {F = F} radius inverse inverseLaw
    (C3.complex3 x y z) =
  Field.complex3Ext (coordinate x) (coordinate y) (coordinate z)
  where
  invC = C3.realEmbed F inverse
  radC = C3.realEmbed F radius

  productIsOne : C3.complexMultiply invC radC ≡ C3.complexOne F
  productIsOne = embeddedRadiusInverse radius inverse inverseLaw

  coordinate : (c : C3.Complex F) →
    C3.complexMultiply invC (C3.complexMultiply radC c) ≡ c
  coordinate c =
    trans
      (sym (Field.complexMultiplyAssociative invC radC c))
      (trans
        (cong (λ coefficient → C3.complexMultiply coefficient c) productIsOne)
        (C3.complexMultiplyOneLeft F c))

------------------------------------------------------------------------
-- Pure helical sectors: normalized curl is +/- identity, hence inverse curl
-- contributes precisely +/- |k|^{-1}.
------------------------------------------------------------------------

normalizedCurlPlusIsIdentity :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (C : ModeRadiusCalibration S k)
    (value : C3.Complex3 F) →
  Normalized.normalizedCurl E S k
    (Helical.helicalProjectorPlus E I S k value)
  ≡ Helical.helicalProjectorPlus E I S k value
normalizedCurlPlusIsIdentity {F = F} E I S L k C value =
  trans
    (cong
      (C3.complex3Scale
        (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (Helical.helicalCurlEigenvaluePlus L k value))
    (nestedInverseRadiusScaleCancels
      (Helical.modeNorm S k)
      (Helical.inverseModeNorm S k)
      (radiusInverse C)
      (Helical.helicalProjectorPlus E I S k value))

normalizedCurlMinusIsNegation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (k : Z3.FourierMode)
    (C : ModeRadiusCalibration S k)
    (value : C3.Complex3 F) →
  Normalized.normalizedCurl E S k
    (Helical.helicalProjectorMinus E I S k value)
  ≡ C3.complex3Negate
      (Helical.helicalProjectorMinus E I S k value)
normalizedCurlMinusIsNegation {F = F} E I S L k C value =
  trans
    (cong
      (C3.complex3Scale
        (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (Helical.helicalCurlEigenvalueMinus L k value))
    (minusScaleCancellation
      (Helical.modeNorm S k)
      (Helical.inverseModeNorm S k)
      (radiusInverse C)
      (Helical.helicalProjectorMinus E I S k value))
  where
  minusScaleCancellation :
    (radius inverse : C3.Carrier F) →
    C3.multiply F radius inverse ≡ C3.one F →
    (u : C3.Complex3 F) →
    C3.complex3Scale (C3.realEmbed F inverse)
      (C3.complex3Scale
        (C3.realEmbed F (C3.negate F radius)) u)
    ≡ C3.complex3Negate u
  minusScaleCancellation radius inverse inverseLaw
      (C3.complex3 x y z) =
    Field.complex3Ext (coordinate x) (coordinate y) (coordinate z)
    where
    invC = C3.realEmbed F inverse
    radC = C3.realEmbed F radius
    negRadC = C3.realEmbed F (C3.negate F radius)

    negativeProduct :
      C3.complexMultiply invC negRadC
      ≡ C3.complexNegate (C3.complexOne F)
    negativeProduct =
      trans
        (cong (C3.complexMultiply invC)
          (sym (C3.realEmbedNegate F radius)))
        (trans
          (Field.complexNegateMultiplyRight invC radC)
          (cong C3.complexNegate
            (embeddedRadiusInverse radius inverse inverseLaw)))

    coordinate : (c : C3.Complex F) →
      C3.complexMultiply invC (C3.complexMultiply negRadC c)
      ≡ C3.complexNegate c
    coordinate c =
      trans
        (sym (Field.complexMultiplyAssociative invC negRadC c))
        (trans
          (cong (λ coefficient → C3.complexMultiply coefficient c)
            negativeProduct)
          (trans
            (Field.complexNegateMultiplyLeft (C3.complexOne F) c)
            (cong C3.complexNegate (C3.complexMultiplyOneLeft F c))))

record MagneticHelicityObserverBoundary : Set where
  constructor magnetic-helicity-observer-boundary
  field
    vectorPotentialUsesSecondInverseRadius : Bool
    vectorPotentialUsesSecondInverseRadiusIsTrue :
      vectorPotentialUsesSecondInverseRadius ≡ true

    plusHelicalNormalizedCurlIdentityOwned : Bool
    plusHelicalNormalizedCurlIdentityOwnedIsTrue :
      plusHelicalNormalizedCurlIdentityOwned ≡ true

    minusHelicalNormalizedCurlNegationOwned : Bool
    minusHelicalNormalizedCurlNegationOwnedIsTrue :
      minusHelicalNormalizedCurlNegationOwned ≡ true

    energyCrossHelicityCompilerDeterminesMagneticHelicity : Bool
    energyCrossHelicityCompilerDeterminesMagneticHelicityIsFalse :
      energyCrossHelicityCompilerDeterminesMagneticHelicity ≡ false

canonicalMagneticHelicityObserverBoundary : MagneticHelicityObserverBoundary
canonicalMagneticHelicityObserverBoundary =
  magnetic-helicity-observer-boundary true refl true refl true refl false refl
