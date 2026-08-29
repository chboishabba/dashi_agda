module DASHI.Physics.Closure.NSTriadKNPhysicalHelicitySignExhaustionRound135Exact where

------------------------------------------------------------------------
-- ROUND135 / EIGHT HELICITY SIGN CLASSES ON THE LITERAL PHYSICAL TRIAD
--
-- Waleffe 1992, DOI: 10.1063/1.858309.
-- Constantin--Majda 1988, DOI: 10.1007/BF01218019.
--
-- Round134 identifies the actual three-leg physical critical production with
-- the Round102 RealField minority-leg algebra.  This file exhausts all eight
-- helicity sign patterns on that SAME object.
--
--   +++ , --- : exactly zero;
--   the six mixed classes : exactly +/- twice the critical-weighted transfer
--   of the unique minority-helicity leg.
--
-- No estimate and no summation occurs here.  The payoff is that the remaining
-- HH->low analysis may now discard homochiral production and work only with
-- three cyclic heterochiral geometries on the literal physical carrier.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (trans)

import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNLiteralThreeLegWaleffeCommonAmplitudeRound93Exact as R93
import DASHI.Physics.Closure.NSTriadKNHeterochiralMinorityLegFieldRound102Exact as R102
import DASHI.Physics.Closure.NSTriadKNPhysicalHeterochiralMinorityWaleffeWeldRound134Exact as R134

data HelicitySign : Set where
  plus minus : HelicitySign

signedRadius :
  ∀ {r} {F : C3.RealField r} →
  HelicitySign → C3.Carrier F → C3.Carrier F
signedRadius {F = F} plus radius = radius
signedRadius {F = F} minus radius = C3.negate F radius

private
  sub : ∀ {r} {F : C3.RealField r} →
    C3.Carrier F → C3.Carrier F → C3.Carrier F
  sub {F = F} x y = C3.add F x (C3.negate F y)

  two : ∀ {r : Level} (F : C3.RealField r) → C3.Carrier F
  two F = C3.add F (C3.one F) (C3.one F)

record PhysicalHelicityRadiusIdentification
    {r} {F : C3.RealField r}
    {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {tau : Physical.PhysicalTriadIncidence}
    (O : R93.LiteralThreeLegHelicalOrbit E I tau) : Set r where
  constructor physical-helicity-radius-identification
  field
    radiusK radiusP radiusQ : C3.Carrier F
    signK signP signQ : HelicitySign
    lambdaKMeaning : R93.lambdaK O ≡ signedRadius signK radiusK
    lambdaPMeaning : R93.lambdaP O ≡ signedRadius signP radiusP
    lambdaQMeaning : R93.lambdaQ O ≡ signedRadius signQ radiusQ

open PhysicalHelicityRadiusIdentification public

minorityNormalForm :
  ∀ {r} {F : C3.RealField r} →
  HelicitySign → HelicitySign → HelicitySign →
  C3.Carrier F → C3.Carrier F → C3.Carrier F → C3.Carrier F →
  C3.Carrier F
minorityNormalForm {F = F} plus plus plus k p q A = C3.zero F
minorityNormalForm {F = F} minus minus minus k p q A = C3.zero F
minorityNormalForm {F = F} minus plus plus k p q A =
  C3.multiply F
    (C3.multiply F (C3.multiply F (two F) k) (sub q p)) A
minorityNormalForm {F = F} plus minus minus k p q A =
  C3.negate F
    (C3.multiply F
      (C3.multiply F (C3.multiply F (two F) k) (sub q p)) A)
minorityNormalForm {F = F} plus minus plus k p q A =
  C3.multiply F
    (C3.multiply F (C3.multiply F (two F) p) (sub k q)) A
minorityNormalForm {F = F} minus plus minus k p q A =
  C3.negate F
    (C3.multiply F
      (C3.multiply F (C3.multiply F (two F) p) (sub k q)) A)
minorityNormalForm {F = F} plus plus minus k p q A =
  C3.multiply F
    (C3.multiply F (C3.multiply F (two F) q) (sub p k)) A
minorityNormalForm {F = F} minus minus plus k p q A =
  C3.negate F
    (C3.multiply F
      (C3.multiply F (C3.multiply F (two F) q) (sub p k)) A)

actualCriticalProductionNormalForm :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (tau : Physical.PhysicalTriadIncidence)
    (O : R93.LiteralThreeLegHelicalOrbit E I tau)
    (H : PhysicalHelicityRadiusIdentification O) →
  R134.actualCriticalProduction E I tau O
    (radiusK H) (radiusP H) (radiusQ H)
  ≡ minorityNormalForm
      (signK H) (signP H) (signQ H)
      (radiusK H) (radiusP H) (radiusQ H) (R93.commonAmplitude O)
actualCriticalProductionNormalForm {F = F} E I tau O H
  rewrite lambdaKMeaning H | lambdaPMeaning H | lambdaQMeaning H
  with signK H | signP H | signQ H
... | plus | plus | plus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.homochiralPlusVanishes
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | minus | minus | minus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.homochiralMinusVanishes
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | minus | plus | plus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.minorityKMinusDifferenceNormalForm
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | plus | minus | minus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.minorityKPlusDifferenceNormalForm
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | plus | minus | plus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.minorityPMinusDifferenceNormalForm
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | minus | plus | minus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.minorityPPlusDifferenceNormalForm
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | plus | plus | minus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.minorityQMinusDifferenceNormalForm
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))
... | minus | minus | plus =
  trans
    (R134.actualCriticalProductionIsMinorityFieldProduction
      E I tau O (radiusK H) (radiusP H) (radiusQ H))
    (R102.minorityQPlusDifferenceNormalForm
      (R134.criticalCell O (radiusK H) (radiusP H) (radiusQ H)))

round135AllEightPhysicalHelicitySignClassesExhausted : Bool
round135AllEightPhysicalHelicitySignClassesExhausted = true

round135PhysicalHomochiralCriticalProductionVanishes : Bool
round135PhysicalHomochiralCriticalProductionVanishes = true

round135PhysicalHeterochiralProductionIsMinorityLegNormalForm : Bool
round135PhysicalHeterochiralProductionIsMinorityLegNormalForm = true

round135CutoffUniformHeterochiralSummationClosed : Bool
round135CutoffUniformHeterochiralSummationClosed = false

round135PackageAClosed : Bool
round135PackageAClosed = false

round135AllEightPhysicalHelicitySignClassesExhaustedIsTrue :
  round135AllEightPhysicalHelicitySignClassesExhausted ≡ true
round135AllEightPhysicalHelicitySignClassesExhaustedIsTrue = refl

round135PackageAClosedIsFalse : round135PackageAClosed ≡ false
round135PackageAClosedIsFalse = refl
