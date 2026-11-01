module DASHI.Physics.Closure.NSTriadKNCriticalRawCurlPhysicalWeldRound170Exact where

------------------------------------------------------------------------
-- ROUND170 / PHYSICAL NORMALIZED-CURL SLOTS = INVERSE RADIUS * RAW CURL SLOT
--
-- This supplies the physical premise consumed by Round169.  Each literal
-- normalized-curl Walsh slot factors its inverseModeNorm scalar outside the
-- trilinear amplitude.  Thus the critical radial coefficient can cancel that
-- inverse exactly using Round147.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact as R140
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142

realOfRealScale :
  ∀ {r} {F : C3.RealField r}
    (a : C3.Carrier F) (z : C3.Complex F) →
  C3.real (C3.complexMultiply (C3.realEmbed F a) z)
  ≡ C3.multiply F a (C3.real z)
realOfRealScale {F = F} a (C3.complex zr zi)
  rewrite Algebra.realMultiplyZeroLeft F zi
        | C3.negateZero F
        | Algebra.realAddZeroRight F (C3.multiply F a zr) = refl

rawCurlSlotK :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Carrier F
rawCurlSlotK E k uK uP uQ =
  R140.realAmplitude (Helical.curlSymbol E k uK) uP uQ

rawCurlSlotP :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Carrier F
rawCurlSlotP E p uK uP uQ =
  R140.realAmplitude uK (Helical.curlSymbol E p uP) uQ

rawCurlSlotQ :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Carrier F
rawCurlSlotQ E q uK uP uQ =
  R140.realAmplitude uK uP (Helical.curlSymbol E q uQ)

normalizedSlotKFactorsInverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) (uK uP uQ : C3.Complex3 F) →
  R140.realAmplitude (R142.normalizedCurl E S k uK) uP uQ
  ≡ C3.multiply F (Helical.inverseModeNorm S k)
      (rawCurlSlotK E k uK uP uQ)
normalizedSlotKFactorsInverse {F = F} E S k uK uP uQ =
  trans
    (cong C3.real
      (Scaling.hermitianPairingScaleLeft
        (C3.realEmbed F (Helical.inverseModeNorm S k))
        (Helical.curlSymbol E k uK)
        (Cross.complex3Cross uP uQ)))
    (trans
      (cong
        (λ scalar → C3.real
          (C3.complexMultiply scalar
            (C3.hermitianPairing3
              (Helical.curlSymbol E k uK)
              (Cross.complex3Cross uP uQ))))
        (C3.realEmbedConjugate F (Helical.inverseModeNorm S k)))
      (realOfRealScale
        (Helical.inverseModeNorm S k)
        (C3.hermitianPairing3
          (Helical.curlSymbol E k uK)
          (Cross.complex3Cross uP uQ))))

normalizedSlotPFactorsInverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (p : Z3.FourierMode) (uK uP uQ : C3.Complex3 F) →
  R140.realAmplitude uK (R142.normalizedCurl E S p uP) uQ
  ≡ C3.multiply F (Helical.inverseModeNorm S p)
      (rawCurlSlotP E p uK uP uQ)
normalizedSlotPFactorsInverse {F = F} E S p uK uP uQ =
  trans
    (cong (λ v → C3.real (C3.hermitianPairing3 uK v))
      (R94.crossScaleLeft
        (C3.realEmbed F (Helical.inverseModeNorm S p))
        (Helical.curlSymbol E p uP) uQ))
    (trans
      (cong C3.real
        (Scaling.hermitianPairingScaleRight
          (C3.realEmbed F (Helical.inverseModeNorm S p))
          uK (Cross.complex3Cross (Helical.curlSymbol E p uP) uQ)))
      (realOfRealScale
        (Helical.inverseModeNorm S p)
        (C3.hermitianPairing3 uK
          (Cross.complex3Cross (Helical.curlSymbol E p uP) uQ))))

normalizedSlotQFactorsInverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (q : Z3.FourierMode) (uK uP uQ : C3.Complex3 F) →
  R140.realAmplitude uK uP (R142.normalizedCurl E S q uQ)
  ≡ C3.multiply F (Helical.inverseModeNorm S q)
      (rawCurlSlotQ E q uK uP uQ)
normalizedSlotQFactorsInverse {F = F} E S q uK uP uQ =
  trans
    (cong (λ v → C3.real (C3.hermitianPairing3 uK v))
      (R94.crossScaleRight
        (C3.realEmbed F (Helical.inverseModeNorm S q))
        uP (Helical.curlSymbol E q uQ)))
    (trans
      (cong C3.real
        (Scaling.hermitianPairingScaleRight
          (C3.realEmbed F (Helical.inverseModeNorm S q))
          uK (Cross.complex3Cross uP (Helical.curlSymbol E q uQ))))
      (realOfRealScale
        (Helical.inverseModeNorm S q)
        (C3.hermitianPairing3 uK
          (Cross.complex3Cross uP (Helical.curlSymbol E q uQ)))))

round170AllNormalizedSlotsFactorInverseRadius : Bool
round170AllNormalizedSlotsFactorInverseRadius = true

round170RawCurlGapProductionPhysicalWeldReady : Bool
round170RawCurlGapProductionPhysicalWeldReady = true

round170RawCurlGapGlobalPaymentClosed : Bool
round170RawCurlGapGlobalPaymentClosed = false

round170PackageAClosed : Bool
round170PackageAClosed = false

round170AllNormalizedSlotsFactorInverseRadiusIsTrue :
  round170AllNormalizedSlotsFactorInverseRadius ≡ true
round170AllNormalizedSlotsFactorInverseRadiusIsTrue = refl

round170PackageAClosedIsFalse : round170PackageAClosed ≡ false
round170PackageAClosedIsFalse = refl
