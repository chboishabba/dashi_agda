module DASHI.Physics.Closure.NSTriadKNHelicityWalshNormalizedCurlWeldRound143Exact where

------------------------------------------------------------------------
-- ROUND143 / WALSH MOMENTS AS LITERAL NORMALIZED-CURL INSERTIONS
--
-- Sources:
--   Zhen Lei; Fang-Hua Lin; Yi Zhou,
--   "Structure of Helicity and Global Solutions of Incompressible
--   Navier-Stokes Equation", ARMA 218 (2015), DOI 10.1007/s00205-015-0884-8.
--   Fabian Waleffe, Physics of Fluids A 4 (1992), DOI 10.1063/1.858309.
--
-- Rounds140/141 identify the first Walsh moments with the differences
-- u_j^+ - u_j^-.  Round142 identifies that difference with |D|^-1 curl.
-- This file performs the same-object physical weld when the +/- components are
-- the repository's actual helical projectors and the three velocity modes are
-- transverse.
--
-- The result is exact:
--
--   M_k = Re < S_k u_k , u_p x u_q >,
--   M_p = Re < u_k , S_p u_p x u_q >,
--   M_q = Re < u_k , u_p x S_q u_q >,
--
-- where S_j = |j|^-1 curl_j on the literal Fourier carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; cong₂; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNPeriodicHelicalFourierInfrastructure as Helical
import DASHI.Physics.Closure.NSTriadKNHelicityWalshMomentRound139Exact as R139
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalAmplitudeRound140Exact as R140
import DASHI.Physics.Closure.NSTriadKNHelicityWalshPhysicalCyclicSlotsRound141Exact as R141
import DASHI.Physics.Closure.NSTriadKNHelicitySignNormalizedCurlRound142Exact as R142

projectorHelicityComponents :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (k p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  R140.HelicityComponents F
projectorHelicityComponents E I S k p q uK uP uQ =
  R140.helicity-components
    (Helical.helicalProjectorPlus E I S k uK)
    (Helical.helicalProjectorMinus E I S k uK)
    (Helical.helicalProjectorPlus E I S p uP)
    (Helical.helicalProjectorMinus E I S p uP)
    (Helical.helicalProjectorPlus E I S q uQ)
    (Helical.helicalProjectorMinus E I S q uQ)

cong3 :
  ∀ {a b c d} {A : Set a} {B : Set b} {C : Set c} {D : Set d}
    (f : A → B → C → D) {x x' y y' z z'} →
  x ≡ x' → y ≡ y' → z ≡ z' → f x y z ≡ f x' y' z'
cong3 f refl refl refl = refl

slotMomentKIsNormalizedCurlAmplitude :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (k p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  Helical.Transverse E k uK →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  R139.slotMomentK
    (R140.physicalEightAmplitudes
      (projectorHelicityComponents E I S k p q uK uP uQ))
  ≡
  R140.realAmplitude
    (R142.normalizedCurl E S k uK) uP uQ
slotMomentKIsNormalizedCurlAmplitude E I S L H k p q uK uP uQ tK tP tQ =
  let
    C = projectorHelicityComponents E I S k p q uK uP uQ
    diffKMeaning = R142.helicitySignActionIsNormalizedCurl E I S H k uK
    totalPMeaning = Helical.velocityHelicalDecomposition L p uP tP
    totalQMeaning = Helical.velocityHelicalDecomposition L q uQ tQ
  in
  trans
    (R140.slotMomentKIsPhysicalDifferenceAmplitude C)
    (cong3 R140.realAmplitude diffKMeaning totalPMeaning totalQMeaning)

slotMomentPIsNormalizedCurlAmplitude :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (k p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  Helical.Transverse E k uK →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  R139.slotMomentP
    (R140.physicalEightAmplitudes
      (projectorHelicityComponents E I S k p q uK uP uQ))
  ≡
  R140.realAmplitude
    uK (R142.normalizedCurl E S p uP) uQ
slotMomentPIsNormalizedCurlAmplitude E I S L H k p q uK uP uQ tK tP tQ =
  let
    C = projectorHelicityComponents E I S k p q uK uP uQ
    totalKMeaning = Helical.velocityHelicalDecomposition L k uK tK
    diffPMeaning = R142.helicitySignActionIsNormalizedCurl E I S H p uP
    totalQMeaning = Helical.velocityHelicalDecomposition L q uQ tQ
  in
  trans
    (R141.slotMomentPIsPhysicalDifferenceAmplitude C)
    (cong3 R140.realAmplitude totalKMeaning diffPMeaning totalQMeaning)

slotMomentQIsNormalizedCurlAmplitude :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (S : Helical.HelicalModeScalars F)
    (L : Helical.PeriodicHelicalProjectorLaws F E I S)
    (H : R142.HelicalHalfCalibration S)
    (k p q : Z3.FourierMode)
    (uK uP uQ : C3.Complex3 F) →
  Helical.Transverse E k uK →
  Helical.Transverse E p uP →
  Helical.Transverse E q uQ →
  R139.slotMomentQ
    (R140.physicalEightAmplitudes
      (projectorHelicityComponents E I S k p q uK uP uQ))
  ≡
  R140.realAmplitude
    uK uP (R142.normalizedCurl E S q uQ)
slotMomentQIsNormalizedCurlAmplitude E I S L H k p q uK uP uQ tK tP tQ =
  let
    C = projectorHelicityComponents E I S k p q uK uP uQ
    totalKMeaning = Helical.velocityHelicalDecomposition L k uK tK
    totalPMeaning = Helical.velocityHelicalDecomposition L p uP tP
    diffQMeaning = R142.helicitySignActionIsNormalizedCurl E I S H q uQ
  in
  trans
    (R141.slotMomentQIsPhysicalDifferenceAmplitude C)
    (cong3 R140.realAmplitude totalKMeaning totalPMeaning diffQMeaning)

round143AllWalshMomentsNormalizedCurlWeldClosed : Bool
round143AllWalshMomentsNormalizedCurlWeldClosed = true

round143NormalizedCurlIsOrderZeroHelicitySignAction : Bool
round143NormalizedCurlIsOrderZeroHelicitySignAction = true

round143PackageAClosed : Bool
round143PackageAClosed = false

round143AllWalshMomentsNormalizedCurlWeldClosedIsTrue :
  round143AllWalshMomentsNormalizedCurlWeldClosed ≡ true
round143AllWalshMomentsNormalizedCurlWeldClosedIsTrue = refl

round143PackageAClosedIsFalse : round143PackageAClosed ≡ false
round143PackageAClosedIsFalse = refl
