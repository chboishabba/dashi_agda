module DASHI.Physics.Closure.NSTriadKNCriticalNetworkSlotInverseFactorRound197Exact where

------------------------------------------------------------------------
-- ROUND197 / NORMALIZED-CURL NETWORK SLOTS FACTOR ONE INVERSE RADIUS
--
-- R196 exposes the complete critical forcing as
--
--   c_k N_k^S + c_p N_p^S + c_q N_q^S.
--
-- Every term of N_j^S contains exactly one normalized-curl insertion in slot
-- j, either on the state or on the forcing vector.  By trilinearity and the
-- reality of inverseModeNorm,
--
--   N_j^S = inv(r_j) N_j^curl
--
-- exactly for j=k,p,q.  Hence the radius carried by the critical coefficient
-- c_j is ready to cancel against the normalized-curl denominator exactly as in
-- R147/R169, now at the NETWORK-FORCING level rather than only the cubic
-- amplitude level.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplexCommutativeRingExact as Ring
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3BeltramiCrossSuppressionRound93Exact as Cross
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNWaleffeAmplitudeDampedNetworkTangentRound94Exact as R94
import DASHI.Physics.Closure.NSTriadKNCriticalDoubleCommutatorNetworkSlotsRound196Exact as R196

rawNetworkSlotK :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
rawNetworkSlotK E k uK uP uQ fK fP fQ =
  R94.networkForcing
    (Helical.curlSymbol E k uK) uP uQ
    (Helical.curlSymbol E k fK) fP fQ

rawNetworkSlotP :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
rawNetworkSlotP E p uK uP uQ fK fP fQ =
  R94.networkForcing
    uK (Helical.curlSymbol E p uP) uQ
    fK (Helical.curlSymbol E p fP) fQ

rawNetworkSlotQ :
  ∀ {r} {F : C3.RealField r} →
  C3.IntegerEmbedding F → Z3.FourierMode →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F →
  C3.Complex3 F → C3.Complex3 F → C3.Complex3 F → C3.Complex F
rawNetworkSlotQ E q uK uP uQ fK fP fQ =
  R94.networkForcing
    uK uP (Helical.curlSymbol E q uQ)
    fK fP (Helical.curlSymbol E q fQ)

networkSlotKFactorsInverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  R196.networkSlotK E S k uK uP uQ fK fP fQ
  ≡ C3.complexMultiply
      (C3.realEmbed F (Helical.inverseModeNorm S k))
      (rawNetworkSlotK E k uK uP uQ fK fP fQ)
networkSlotKFactorsInverse {F = F} E S k uK uP uQ fK fP fQ =
  let
    s = C3.realEmbed F (Helical.inverseModeNorm S k)
    cu = Helical.curlSymbol E k uK
    cf = Helical.curlSymbol E k fK
    x = C3.hermitianPairing3 cf (Cross.complex3Cross uP uQ)
    y = C3.hermitianPairing3 cu (Cross.complex3Cross fP uQ)
    z = C3.hermitianPairing3 cu (Cross.complex3Cross uP fQ)
  in
  trans
    (cong
      (λ value →
        C3.complexAdd
          (C3.complexAdd value
            (C3.hermitianPairing3 (C3.complex3Scale s cu)
              (Cross.complex3Cross fP uQ)))
          (C3.hermitianPairing3 (C3.complex3Scale s cu)
            (Cross.complex3Cross uP fQ)))
      (trans
        (Scaling.hermitianPairingScaleLeft s cf (Cross.complex3Cross uP uQ))
        (cong (λ scalar → C3.complexMultiply scalar x)
          (C3.realEmbedConjugate F (Helical.inverseModeNorm S k)))))
    (trans
      (cong
        (λ value →
          C3.complexAdd
            (C3.complexAdd (C3.complexMultiply s x) value)
            (C3.hermitianPairing3 (C3.complex3Scale s cu)
              (Cross.complex3Cross uP fQ)))
        (trans
          (Scaling.hermitianPairingScaleLeft s cu (Cross.complex3Cross fP uQ))
          (cong (λ scalar → C3.complexMultiply scalar y)
            (C3.realEmbedConjugate F (Helical.inverseModeNorm S k)))))
      (trans
        (cong
          (C3.complexAdd
            (C3.complexAdd (C3.complexMultiply s x) (C3.complexMultiply s y)))
          (trans
            (Scaling.hermitianPairingScaleLeft s cu (Cross.complex3Cross uP fQ))
            (cong (λ scalar → C3.complexMultiply scalar z)
              (C3.realEmbedConjugate F (Helical.inverseModeNorm S k)))))
        (R.solve 4
          (λ s x y z →
            (((s R.⊗ x) R.⊕ (s R.⊗ y)) R.⊕ (s R.⊗ z))
            R.⊜ s R.⊗ ((x R.⊕ y) R.⊕ z))
          refl s x y z)))
  where module R = Ring.Solver F

networkSlotPFactorsInverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (p : Z3.FourierMode)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  R196.networkSlotP E S p uK uP uQ fK fP fQ
  ≡ C3.complexMultiply
      (C3.realEmbed F (Helical.inverseModeNorm S p))
      (rawNetworkSlotP E p uK uP uQ fK fP fQ)
networkSlotPFactorsInverse {F = F} E S p uK uP uQ fK fP fQ =
  let
    s = C3.realEmbed F (Helical.inverseModeNorm S p)
    cu = Helical.curlSymbol E p uP
    cf = Helical.curlSymbol E p fP
    x = C3.hermitianPairing3 fK (Cross.complex3Cross cu uQ)
    y = C3.hermitianPairing3 uK (Cross.complex3Cross cf uQ)
    z = C3.hermitianPairing3 uK (Cross.complex3Cross cu fQ)
  in
  rewrite R94.crossScaleLeft s cu uQ
        | R94.crossScaleLeft s cf uQ
        | R94.crossScaleLeft s cu fQ
        | Scaling.hermitianPairingScaleRight s fK (Cross.complex3Cross cu uQ)
        | Scaling.hermitianPairingScaleRight s uK (Cross.complex3Cross cf uQ)
        | Scaling.hermitianPairingScaleRight s uK (Cross.complex3Cross cu fQ) =
    R.solve 4
      (λ s x y z →
        (((s R.⊗ x) R.⊕ (s R.⊗ y)) R.⊕ (s R.⊗ z))
        R.⊜ s R.⊗ ((x R.⊕ y) R.⊕ z))
      refl s x y z
  where module R = Ring.Solver F

networkSlotQFactorsInverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) (S : Helical.HelicalModeScalars F)
    (q : Z3.FourierMode)
    (uK uP uQ fK fP fQ : C3.Complex3 F) →
  R196.networkSlotQ E S q uK uP uQ fK fP fQ
  ≡ C3.complexMultiply
      (C3.realEmbed F (Helical.inverseModeNorm S q))
      (rawNetworkSlotQ E q uK uP uQ fK fP fQ)
networkSlotQFactorsInverse {F = F} E S q uK uP uQ fK fP fQ =
  let
    s = C3.realEmbed F (Helical.inverseModeNorm S q)
    cu = Helical.curlSymbol E q uQ
    cf = Helical.curlSymbol E q fQ
    x = C3.hermitianPairing3 fK (Cross.complex3Cross uP cu)
    y = C3.hermitianPairing3 uK (Cross.complex3Cross fP cu)
    z = C3.hermitianPairing3 uK (Cross.complex3Cross uP cf)
  in
  rewrite R94.crossScaleRight s uP cu
        | R94.crossScaleRight s fP cu
        | R94.crossScaleRight s uP cf
        | Scaling.hermitianPairingScaleRight s fK (Cross.complex3Cross uP cu)
        | Scaling.hermitianPairingScaleRight s uK (Cross.complex3Cross fP cu)
        | Scaling.hermitianPairingScaleRight s uK (Cross.complex3Cross uP cf) =
    R.solve 4
      (λ s x y z →
        (((s R.⊗ x) R.⊕ (s R.⊗ y)) R.⊕ (s R.⊗ z))
        R.⊜ s R.⊗ ((x R.⊕ y) R.⊕ z))
      refl s x y z
  where module R = Ring.Solver F

round197AllNetworkSlotsFactorOneInverseRadius : Bool
round197AllNetworkSlotsFactorOneInverseRadius = true

round197AnyExtraNormalizedCurlDenominatorSurvives : Bool
round197AnyExtraNormalizedCurlDenominatorSurvives = false

round197CriticalCoefficientRadiusCancellationReady : Bool
round197CriticalCoefficientRadiusCancellationReady = true

round197PackageAClosed : Bool
round197PackageAClosed = false

round197ClayPromotion : Bool
round197ClayPromotion = false
