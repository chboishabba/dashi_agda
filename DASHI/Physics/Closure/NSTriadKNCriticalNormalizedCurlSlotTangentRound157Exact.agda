module DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlSlotTangentRound157Exact where

------------------------------------------------------------------------
-- ROUND157 / DAMPED-FORCED EVOLUTION OF THE NORMALIZED-CURL SLOT DIFFERENCE
--
-- Source:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Zhen Lei; Fang-Hua Lin; Yi Zhou, ARMA 218 (2015),
--   DOI 10.1007/s00205-015-0884-8.
--
-- Round94 already proves the exact damped-forced tangent equation for the
-- literal cubic amplitude Z=<u_k,u_p x u_q>.  Round144 shows that package A
-- only sees differences between normalized-curl insertions in two slots.
--
-- This file joins those facts rather than inventing a new trajectory receipt.
-- First, normalized curl S_j=|j|^-1 curl_j is proved additive and complex-
-- linear on the exact C3 carrier.  Hence it commutes with the literal
-- damped-plus-forcing decomposition.
--
-- Then for
--
--   B_k = <S_k u_k, u_p x u_q>,
--   B_q = <u_k, u_p x S_q u_q>,
--
-- their exact difference obeys
--
--   d(B_k-B_q)
--     = -rhoSum (B_k-B_q)
--       + (F_k^S-F_q^S),
--
-- where the forcing terms are the ACTUAL Round94 three-slot network forcing
-- with normalized curl inserted in the corresponding state/forcing slot.
--
-- This is the trajectory equation requested after Round153.  The remaining
-- A theorem is no longer "find a dynamics": it is to prove that the complete
-- signed forcing-difference network has a cutoff-uniform quadratic-variation
-- payment after the Round154 nuisance quotient and Round155 telescope.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Field
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNHelicalModeNormSquareActionRound126Exact as R126
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94

------------------------------------------------------------------------
-- Exact C3 linearity needed by normalized curl.
------------------------------------------------------------------------

complex3ScaleAdd :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (u v : C3.Complex3 F) →
  C3.complex3Scale scalar (C3.complex3Add u v)
  ≡ C3.complex3Add
      (C3.complex3Scale scalar u)
      (C3.complex3Scale scalar v)
complex3ScaleAdd {F = F} scalar
    (C3.complex3 ux uy uz) (C3.complex3 vx vy vz) =
  Field.complex3Ext
    (R.solve 3 (λ s u v → s R.⊗ (u R.⊕ v) R.⊜ (s R.⊗ u) R.⊕ (s R.⊗ v))
      refl scalar ux vx)
    (R.solve 3 (λ s u v → s R.⊗ (u R.⊕ v) R.⊜ (s R.⊗ u) R.⊕ (s R.⊗ v))
      refl scalar uy vy)
    (R.solve 3 (λ s u v → s R.⊗ (u R.⊕ v) R.⊜ (s R.⊗ u) R.⊕ (s R.⊗ v))
      refl scalar uz vz)
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
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  Helical.curlSymbol E k (C3.complex3Add u v)
  ≡ C3.complex3Add (Helical.curlSymbol E k u) (Helical.curlSymbol E k v)
curlSymbolAdd {F = F} E k u v =
  trans
    (cong (C3.complex3Scale (C3.complexI F))
      (R94.crossAddRight (C3.modeVector E k) u v))
    (complex3ScaleAdd (C3.complexI F)
      (R94.Cross.complex3Cross (C3.modeVector E k) u)
      (R94.Cross.complex3Cross (C3.modeVector E k) v))

normalizedCurlAdd :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (u v : C3.Complex3 F) →
  R142.normalizedCurl E S k (C3.complex3Add u v)
  ≡ C3.complex3Add
      (R142.normalizedCurl E S k u)
      (R142.normalizedCurl E S k v)
normalizedCurlAdd {F = F} E S k u v =
  trans
    (cong
      (C3.complex3Scale
        (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (curlSymbolAdd E k u v))
    (complex3ScaleAdd
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (Helical.curlSymbol E k u)
      (Helical.curlSymbol E k v))

normalizedCurlScale :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (scalar : C3.Complex F)
    (u : C3.Complex3 F) →
  R142.normalizedCurl E S k (C3.complex3Scale scalar u)
  ≡ C3.complex3Scale scalar (R142.normalizedCurl E S k u)
normalizedCurlScale {F = F} E S k scalar u =
  trans
    (cong
      (C3.complex3Scale
        (C3.realEmbed F (Helical.inverseModeNorm S k)))
      (R126.curlSymbolScale E k scalar u))
    (complex3ScaleNestedCommutes
      (C3.realEmbed F (Helical.inverseModeNorm S k)) scalar
      (Helical.curlSymbol E k u))

normalizedCurlDampedPlusForcing :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (rho : C3.Carrier F)
    (u f : C3.Complex3 F) →
  R142.normalizedCurl E S k (R94.dampedPlusForcing rho u f)
  ≡ R94.dampedPlusForcing rho
      (R142.normalizedCurl E S k u)
      (R142.normalizedCurl E S k f)
normalizedCurlDampedPlusForcing E S k rho u f =
  trans
    (normalizedCurlAdd E S k
      (C3.complex3Scale (R94.negativeReal rho) u) f)
    (cong₂ C3.complex3Add
      (normalizedCurlScale E S k (R94.negativeReal rho) u)
      refl)

------------------------------------------------------------------------
-- Exact damped-forced equation for the two surviving physical slot channels.
------------------------------------------------------------------------

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
  C3.complexSubtract
    (slotKAmplitude E S k uK uP uQ)
    (slotQAmplitude E S q uK uP uQ)

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
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k q : Z3.FourierMode)
    (rhoK rhoP rhoQ : C3.Carrier F)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  slotDifferenceTangent E S k q uK uP uQ
    (R94.dampedPlusForcing rhoK uK fK)
    (R94.dampedPlusForcing rhoP uP fP)
    (R94.dampedPlusForcing rhoQ uQ fQ)
  ≡
  C3.complexAdd
    (C3.complexMultiply
      (R94.totalNegativeDecay rhoK rhoP rhoQ)
      (slotDifference E S k q uK uP uQ))
    (slotDifferenceNetworkForcing E S k q uK uP uQ fK fP fQ)
slotDifferenceDampedNetworkEquation {F = F}
    E S k q rhoK rhoP rhoQ uK uP uQ fK fP fQ
  rewrite normalizedCurlDampedPlusForcing E S k rhoK uK fK
        | normalizedCurlDampedPlusForcing E S q rhoQ uQ fQ =
  trans
    (cong₂ C3.complexSubtract
      (R94.amplitudeTangentDampedNetwork
        rhoK rhoP rhoQ
        (R142.normalizedCurl E S k uK) uP uQ
        (R142.normalizedCurl E S k fK) fP fQ)
      (R94.amplitudeTangentDampedNetwork
        rhoK rhoP rhoQ
        uK uP (R142.normalizedCurl E S q uQ)
        fK fP (R142.normalizedCurl E S q fQ)))
    regroup
  where
  decay = R94.totalNegativeDecay rhoK rhoP rhoQ
  aK = slotKAmplitude E S k uK uP uQ
  aQ = slotQAmplitude E S q uK uP uQ
  fKS = R94.networkForcing
    (R142.normalizedCurl E S k uK) uP uQ
    (R142.normalizedCurl E S k fK) fP fQ
  fQS = R94.networkForcing
    uK uP (R142.normalizedCurl E S q uQ)
    fK fP (R142.normalizedCurl E S q fQ)

  regroup :
    C3.complexSubtract
      (C3.complexAdd (C3.complexMultiply decay aK) fKS)
      (C3.complexAdd (C3.complexMultiply decay aQ) fQS)
    ≡
    C3.complexAdd
      (C3.complexMultiply decay (C3.complexSubtract aK aQ))
      (C3.complexSubtract fKS fQS)
  regroup =
    R.solve 5
      (λ decay aK aQ fK fQ →
        (((decay R.⊗ aK) R.⊕ fK)
          R.⊕ (R.⊝ ((decay R.⊗ aQ) R.⊕ fQ)))
        R.⊜
        ((decay R.⊗ (aK R.⊕ (R.⊝ aQ)))
          R.⊕ (fK R.⊕ (R.⊝ fQ))))
      refl decay aK aQ fKS fQS
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
