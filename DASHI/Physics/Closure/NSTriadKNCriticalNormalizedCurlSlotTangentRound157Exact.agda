module DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact where

------------------------------------------------------------------------
-- ROUND157 / DAMPED-FORCED NORMALIZED-CURL SLOT DIFFERENCE
--
-- Waleffe 1992, DOI 10.1063/1.858309.
-- Lei--Lin--Zhou 2015, DOI 10.1007/s00205-015-0884-8.
--
-- Round94 owns the literal damped-forced cubic-amplitude tangent.  Round144
-- shows the critical production only sees normalized-curl slot differences.
-- Here normalized curl is proved complex-linear and the Round94 equation is
-- transported to B_k-B_q exactly, with the forcing difference left signed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNHelicalModeNormSquareActionRound126Exact as R126
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94

complex3ScaleAdd :
  ∀ {r} {F : C3.RealField r}
    (s : C3.Complex F) (u v : C3.Complex3 F) →
  C3.complex3Scale s (C3.complex3Add u v)
  ≡ C3.complex3Add (C3.complex3Scale s u) (C3.complex3Scale s v)
complex3ScaleAdd {F = F} s
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (R.solve 3 (λ s u v → s R.⊗ (u R.⊕ v) R.⊜ (s R.⊗ u) R.⊕ (s R.⊗ v)) refl s ux vx)
    (R.solve 3 (λ s u v → s R.⊗ (u R.⊕ v) R.⊜ (s R.⊗ u) R.⊕ (s R.⊗ v)) refl s uy vy)
    (R.solve 3 (λ s u v → s R.⊗ (u R.⊕ v) R.⊜ (s R.⊗ u) R.⊕ (s R.⊗ v)) refl s uz vz)
  where module R = Ring.Solver F

complex3ScaleNestedCommutes :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) (u : C3.Complex3 F) →
  C3.complex3Scale a (C3.complex3Scale b u)
  ≡ C3.complex3Scale b (C3.complex3Scale a u)
complex3ScaleNestedCommutes {F = F} a b (C3.complex3 ux uy uz) =
  Field.complex3Ext
    (R.solve 3 (λ a b u → a R.⊗ (b R.⊗ u) R.⊜ b R.⊗ (a R.⊗ u)) refl a b ux)
    (R.solve 3 (λ a b u → a R.⊗ (b R.⊗ u) R.⊜ b R.⊗ (a R.⊗ u)) refl a b uy)
    (R.solve 3 (λ a b u → a R.⊗ (b R.⊗ u) R.⊜ b R.⊗ (a R.⊗ u)) refl a b uz)
  where module R = Ring.Solver F

curlSymbolAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.curlSymbol E k (C3.complex3Add u v)
  ≡ C3.complex3Add (Helical.curlSymbol E k u) (Helical.curlSymbol E k v)
curlSymbolAdd {F = F} E k u v =
  trans
    (cong (C3.complex3Scale (C3.complexI F))
      (R94.crossAddRight (C3.modeVector E k) u v))
    (complex3ScaleAdd (C3.complexI F)
      (Cross.complex3Cross (C3.modeVector E k) u)
      (Cross.complex3Cross (C3.modeVector E k) v))

normalizedCurlAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) (u v : C3.Complex3 F) →
  R142.normalizedCurl E S k (C3.complex3Add u v)
  ≡ C3.complex3Add (R142.normalizedCurl E S k u) (R142.normalizedCurl E S k v)
normalizedCurlAdd {F = F} E S k u v =
  trans
    (cong
      (C3.complex3Scale (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (curlSymbolAdd E k u v))
    (complex3ScaleAdd
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (Helical.curlSymbol E k u) (Helical.curlSymbol E k v))

normalizedCurlScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) (s : C3.Complex F) (u : C3.Complex3 F) →
  R142.normalizedCurl E S k (C3.complex3Scale s u)
  ≡ C3.complex3Scale s (R142.normalizedCurl E S k u)
normalizedCurlScale {F = F} E S k s u =
  trans
    (cong
      (C3.complex3Scale (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (R126.curlSymbolScale E k s u))
    (complex3ScaleNestedCommutes
      (C3.realEmbed F (Helical.inverseModeNorm S k)) s
      (Helical.curlSymbol E k u))

normalizedCurlDampedPlusForcing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode) (rho : C3.Carrier F)
    (u f : C3.Complex3 F) →
  R142.normalizedCurl E S k (R94.dampedPlusForcing rho u f)
  ≡ R94.dampedPlusForcing rho
      (R142.normalizedCurl E S k u) (R142.normalizedCurl E S k f)
normalizedCurlDampedPlusForcing E S k rho u f =
  trans
    (normalizedCurlAdd E S k (C3.complex3Scale (R94.negativeReal rho) u) f)
    (cong₂ C3.complex3Add
      (normalizedCurlScale E S k (R94.negativeReal rho) u) refl)

slotKAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotKAmplitude E S k uK uP uQ =
  R94.complexAmplitude (R142.normalizedCurl E S k uK) uP uQ

slotQAmplitude :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotQAmplitude E S q uK uP uQ =
  R94.complexAmplitude uK uP (R142.normalizedCurl E S q uQ)

slotDifference :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotDifference E S k q uK uP uQ =
  C3.complexSubtract (slotKAmplitude E S k uK uP uQ) (slotQAmplitude E S q uK uP uQ)

slotDifferenceTangent :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotDifferenceTangent E S k q uK uP uQ dK dP dQ =
  C3.complexSubtract
    (R94.amplitudeTangent
      (R142.normalizedCurl E S k uK) uP uQ
      (R142.normalizedCurl E S k dK) dP dQ)
    (R94.amplitudeTangent
      uK uP (R142.normalizedCurl E S q uQ)
      dK dP (R142.normalizedCurl E S q dQ))

slotDifferenceNetworkForcing :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Helical.HelicalModeScalars F →
  Z3.FourierMode → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ =
  C3.complexSubtract
    (R94.networkForcing
      (R142.normalizedCurl E S k uK) uP uQ
      (R142.normalizedCurl E S k fK) fP fQ)
    (R94.networkForcing
      uK uP (R142.normalizedCurl E S q uQ)
      fK fP (R142.normalizedCurl E S q fQ))

slotDifferenceDampedNetworkEquation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k q : Z3.FourierMode) (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  slotDifferenceTangent E S k q uK uP uQ
    (R94.dampedPlusForcing rhoK uK fK)
    (R94.dampedPlusForcing rhoP uP fP)
    (R94.dampedPlusForcing rhoQ uQ fQ)
  ≡ C3.complexAdd
      (C3.complexMultiply (R94.totalNegativeDecay rhoK rhoP rhoQ)
        (slotDifference E S k q uK uP uQ))
      (slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ)
slotDifferenceDampedNetworkEquation {F = F}
    E S k q rhoK rhoP rhoQ uK uP uQ fK fP fQ
  rewrite normalizedCurlDampedPlusForcing E S k rhoK uK fK
        | normalizedCurlDampedPlusForcing E S q rhoQ uQ fQ =
  trans
    (cong₂ C3.complexSubtract
      (R94.amplitudeTangentDampedNetwork rhoK rhoP rhoQ
        (R142.normalizedCurl E S k uK) uP uQ
        (R142.normalizedCurl E S k fK) fP fQ)
      (R94.amplitudeTangentDampedNetwork rhoK rhoP rhoQ
        uK uP (R142.normalizedCurl E S q uQ)
        fK fP (R142.normalizedCurl E S q fQ)))
    regroup
  where
  d = R94.totalNegativeDecay rhoK rhoP rhoQ
  a = slotKAmplitude E S k uK uP uQ
  b = slotQAmplitude E S q uK uP uQ
  fa = R94.networkForcing
    (R142.normalizedCurl E S k uK) uP uQ
    (R142.normalizedCurl E S k fK) fP fQ
  fb = R94.networkForcing
    uK uP (R142.normalizedCurl E S q uQ)
    fK fP (R142.normalizedCurl E S q fQ)
  regroup :
    C3.complexSubtract
      (C3.complexAdd (C3.complexMultiply d a) fa)
      (C3.complexAdd (C3.complexMultiply d b) fb)
    ≡ C3.complexAdd
      (C3.complexMultiply d (C3.complexSubtract a b))
      (C3.complexSubtract fa fb)
  regroup =
    R.solve 5
      (λ d a b fa fb →
        (((d R.⊗ a) R.⊕ fa) R.⊕ (R.⊝ ((d R.⊗ b) R.⊕ fb)))
        R.⊜ ((d R.⊗ (a R.⊕ (R.⊝ b))) R.⊕ (fa R.⊕ (R.⊝ fb))))
      refl d a b fa fb
    where module R = Ring.Solver F

round157NormalizedCurlComplexLinearityClosed : Bool
round157NormalizedCurlComplexLinearityClosed = true
round157SlotDifferenceDampedForcedEquationClosed : Bool
round157SlotDifferenceDampedForcedEquationClosed = true
round157ActualRound94NetworkForcingDifferenceExposed : Bool
round157ActualRound94NetworkForcingDifferenceExposed = true
round157PhysicalForcingQuadraticVariationPaymentClosed : Bool
round157PhysicalForcingQuadraticVariationPaymentClosed = false
round157PackageAClosed : Bool
round157PackageAClosed = false

round157SlotDifferenceDampedForcedEquationClosedIsTrue :
  round157SlotDifferenceDampedForcedEquationClosed ≡ true
round157SlotDifferenceDampedForcedEquationClosedIsTrue = refl
round157PackageAClosedIsFalse : round157PackageAClosed ≡ false
round157PackageAClosedIsFalse = refl
