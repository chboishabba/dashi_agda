module DASHI.Physics.Closure.NSTriadKNCriticalNormalizedCurlDoubleCommutatorRound144Exact where

------------------------------------------------------------------------
-- ROUND144 / COMPLETE EIGHT-CHANNEL CRITICAL PRODUCTION AS TWO PHYSICAL
-- NORMALIZED-CURL SLOT DIFFERENCES
--
-- Sources:
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--   Zhen Lei; Fang-Hua Lin; Yi Zhou, ARMA 218 (2015),
--   DOI 10.1007/s00205-015-0884-8.
--
-- R139: all eight helicity channels collapse to three first Walsh moments.
-- R138: the three radial coefficients sum to zero, so only TWO slot
--       differences survive.
-- R143: each Walsh moment is the literal insertion of S_j=|j|^-1 curl_j.
--
-- Combining these gives, on the actual helical-projector components,
--
--   Pcrit
--    = c_k (B_k-B_q) + c_p (B_p-B_q),
--
-- where
--
--   B_k = Re <S_k u_k, u_p x u_q>,
--   B_p = Re <u_k, S_p u_p x u_q>,
--   B_q = Re <u_k, u_p x S_q u_q>.
--
-- This is the exact "double commutator" surface: a radial multiplier
-- difference is multiplied by a helicity-sign/normalized-curl slot difference.
-- No absolute value is taken before either cancellation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicityWalshMomentRound139Exact as R139
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact as R140
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142
import DASHI.Physics.Closure.NSTriadKNHelicityWalshNormalizedCurlWeldRound143Exact as R143
import DASHI.Physics.Closure.NSTriadKNCriticalHelicitySlotCommutatorRound138Exact as R138

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

cong3 :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B → C → D) {x x' y y' z z'} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong3 f refl refl refl = refl

normalizedCurlSlotK :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (k : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) → C3.Carrier F
normalizedCurlSlotK E S k uK uP uQ =
  R140.realAmplitude (R142.normalizedCurl E S k uK) uP uQ

normalizedCurlSlotP :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (p : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) → C3.Carrier F
normalizedCurlSlotP E S p uK uP uQ =
  R140.realAmplitude uK (R142.normalizedCurl E S p uP) uQ

normalizedCurlSlotQ :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (S : Helical.HelicalModeScalars F)
    (q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) → C3.Carrier F
normalizedCurlSlotQ E S q uK uP uQ =
  R140.realAmplitude uK uP (R142.normalizedCurl E S q uQ)

record PhysicalNormalizedCurlTriad
    {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S) : Set r where
  constructor physical-normalized-curl-triad
  field
    k p q : Z3.FourierMode
    uK uP uQ : C3.Complex3 F
    transverseK : Helical.Transverse E k uK
    transverseP : Helical.Transverse E p uP
    transverseQ : Helical.Transverse E q uQ

open PhysicalNormalizedCurlTriad public

projectorComponents :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S} →
  PhysicalNormalizedCurlTriad E I S L H → R140.HelicityComponents F
projectorComponents {E = E} {I = I} {S = S} T =
  R143.projectorHelicityComponents E I S
    (k T) (p T) (q T) (uK T) (uP T) (uQ T)

criticalProductionIsNormalizedCurlSlotProduction :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (rk rp rq : C3.Carrier F)
    (T : PhysicalNormalizedCurlTriad E I S L H) →
  R139.eightChannelCriticalProduction rk rp rq
    (R140.physicalEightAmplitudes (projectorComponents T))
  ≡
  R138.helicitySlotProduction rk rp rq
    (normalizedCurlSlotK E S (k T) (uK T) (uP T) (uQ T))
    (normalizedCurlSlotP E S (p T) (uK T) (uP T) (uQ T))
    (normalizedCurlSlotQ E S (q T) (uK T) (uP T) (uQ T))
criticalProductionIsNormalizedCurlSlotProduction
    {E = E} {I = I} {S = S} {L = L} {H = H} rk rp rq T =
  let
    C = projectorComponents T
    kMoment = R143.slotMomentKIsNormalizedCurlAmplitude
      E I S L H (k T) (p T) (q T) (uK T) (uP T) (uQ T)
      (transverseK T) (transverseP T) (transverseQ T)
    pMoment = R143.slotMomentPIsNormalizedCurlAmplitude
      E I S L H (k T) (p T) (q T) (uK T) (uP T) (uQ T)
      (transverseK T) (transverseP T) (transverseQ T)
    qMoment = R143.slotMomentQIsNormalizedCurlAmplitude
      E I S L H (k T) (p T) (q T) (uK T) (uP T) (uQ T)
      (transverseK T) (transverseP T) (transverseQ T)
  in
  trans
    (R139.eightChannelsCollapseToFirstWalshMoments
      rk rp rq (R140.physicalEightAmplitudes C))
    (cong3
      (R138.helicitySlotProduction rk rp rq)
      kMoment pMoment qMoment)

criticalProductionIsTwoNormalizedCurlSlotDifferences :
  ∀ {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {S : Helical.HelicalModeScalars F}
    {L : Helical.PeriodicHelicalProjectorLaws F E I S}
    {H : R142.HelicalHalfCalibration S}
    (rk rp rq : C3.Carrier F)
    (T : PhysicalNormalizedCurlTriad E I S L H) →
  R139.eightChannelCriticalProduction rk rp rq
    (R140.physicalEightAmplitudes (projectorComponents T))
  ≡
  C3.add F
    (C3.multiply F
      (R138.criticalRadialCoefficientK rk rp rq)
      (sub
        (normalizedCurlSlotK E S (k T) (uK T) (uP T) (uQ T))
        (normalizedCurlSlotQ E S (q T) (uK T) (uP T) (uQ T))))
    (C3.multiply F
      (R138.criticalRadialCoefficientP rk rp rq)
      (sub
        (normalizedCurlSlotP E S (p T) (uK T) (uP T) (uQ T))
        (normalizedCurlSlotQ E S (q T) (uK T) (uP T) (uQ T))))
criticalProductionIsTwoNormalizedCurlSlotDifferences
    {E = E} {S = S} rk rp rq T =
  trans
    (criticalProductionIsNormalizedCurlSlotProduction rk rp rq T)
    (R138.helicitySlotCommutatorForm
      rk rp rq
      (normalizedCurlSlotK E S (k T) (uK T) (uP T) (uQ T))
      (normalizedCurlSlotP E S (p T) (uK T) (uP T) (uQ T))
      (normalizedCurlSlotQ E S (q T) (uK T) (uP T) (uQ T)))

round144EightChannelPhysicalDoubleCommutatorClosed : Bool
round144EightChannelPhysicalDoubleCommutatorClosed = true

round144AbsoluteValueTakenBeforeWalshOrSlotCancellation : Bool
round144AbsoluteValueTakenBeforeWalshOrSlotCancellation = false

round144PackageAClosed : Bool
round144PackageAClosed = false

round144EightChannelPhysicalDoubleCommutatorClosedIsTrue :
  round144EightChannelPhysicalDoubleCommutatorClosed ≡ true
round144EightChannelPhysicalDoubleCommutatorClosedIsTrue = refl

round144PackageAClosedIsFalse : round144PackageAClosed ≡ false
round144PackageAClosedIsFalse = refl
