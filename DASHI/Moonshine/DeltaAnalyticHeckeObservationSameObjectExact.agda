module DASHI.Moonshine.DeltaAnalyticHeckeObservationSameObjectExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Jean-Pierre Serre, "A Course in Arithmetic", Graduate Texts in
-- Mathematics 7, Springer, 1973.
-- DOI: 10.1007/978-1-4684-9884-4.
--
-- Toshitsune Miyake, "Modular Forms", Springer Monographs in Mathematics,
-- 2006. DOI: 10.1007/3-540-29593-3.
--
-- DASHI CONTRIBUTION
--
-- The repository already had two strong but parallel Delta lanes:
--
--   analytic:  E4^3-E6^2 transforms at weight 12 under every SL2(Z) element;
--   arithmetic: concrete tau(3), tau(9), tau(27) satisfy the weight-12 Hecke
--               prime-power recurrence.
--
-- This file makes the required SAME-OBJECT seam explicit without asking for
-- the recurrence again.  One family of coefficient-identification proofs on
-- the three 3-power observations transports the already-proved tau recurrence
-- to the analytic object's coefficient readout.
--
-- It does not pretend that DASHI has yet constructed the q-expansion
-- coefficient extractor for eta^24.  That extractor/identification is the
-- remaining analytic-arithmetic producer.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Integer using (ℤ; +_)
  renaming (_*_ to _*ℤ_; _-_ to _-ℤ_)
open import Relation.Binary.PropositionalEquality using (cong₂; sym; trans)

import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as Eisenstein
import DASHI.Moonshine.EisensteinDiscriminantWeight12Exact as Disc
import DASHI.Moonshine.DeltaNormalizedWeight12SameObjectExact as Analytic
import DASHI.Moonshine.RamanujanTauHecke23Exact as Tau

------------------------------------------------------------------------
-- Three concrete observations are enough to expose the existing 3-power
-- recurrence while keeping one extensional same-object identification family.
------------------------------------------------------------------------

data ThreePowerObservation : Set where
  at3 at9 at27 : ThreePowerObservation

tauThreePowerReadout : ThreePowerObservation → ℤ
tauThreePowerReadout at3 = Tau.tau3
tauThreePowerReadout at9 = Tau.tau9
tauThreePowerReadout at27 = Tau.tau27

record DeltaCoefficientReadout : Set₁ where
  field
    coefficient : ThreePowerObservation → ℤ
    sameTauCoefficient :
      (observation : ThreePowerObservation) →
      coefficient observation ≡ tauThreePowerReadout observation

open DeltaCoefficientReadout public

coefficientAt3 : DeltaCoefficientReadout → ℤ
coefficientAt3 readout = coefficient readout at3

coefficientAt9 : DeltaCoefficientReadout → ℤ
coefficientAt9 readout = coefficient readout at9

coefficientAt27 : DeltaCoefficientReadout → ℤ
coefficientAt27 readout = coefficient readout at27

coefficient9HeckeRecurrence :
  (readout : DeltaCoefficientReadout) →
  coefficientAt9 readout
  ≡ coefficientAt3 readout *ℤ coefficientAt3 readout -ℤ Tau.pow3Eleven
coefficient9HeckeRecurrence readout =
  trans
    (sameTauCoefficient readout at9)
    (trans
      Tau.tau9PrimeSquareRecurrence
      (cong₂
        (λ left right → left *ℤ right -ℤ Tau.pow3Eleven)
        (sym (sameTauCoefficient readout at3))
        (sym (sameTauCoefficient readout at3))))

coefficient27HeckeRecurrence :
  (readout : DeltaCoefficientReadout) →
  coefficientAt27 readout
  ≡
    (coefficientAt3 readout *ℤ coefficientAt3 readout *ℤ coefficientAt3 readout)
      -ℤ ((+ 2 *ℤ Tau.pow3Eleven) *ℤ coefficientAt3 readout)
coefficient27HeckeRecurrence readout =
  trans
    (sameTauCoefficient readout at27)
    (trans
      Tau.tau27PrimeCubeRecurrence
      (cong₂ _-ℤ_
        (cong₂ _*ℤ_
          (cong₂ _*ℤ_
            (sym (sameTauCoefficient readout at3))
            (sym (sameTauCoefficient readout at3)))
          (sym (sameTauCoefficient readout at3)))
        (cong₂ _*ℤ_
          refl
          (sym (sameTauCoefficient readout at3)))))

------------------------------------------------------------------------
-- Same analytic Delta carrier + coefficient observation.
------------------------------------------------------------------------

record DeltaAnalyticArithmeticSameObject
    (M : Eisenstein.EisensteinAnalyticModel)
    (A : Disc.DiscriminantAlgebra M)
    (N : Analytic.WeightCompatibleNormalization M) : Set₁ where
  field
    eta24SameObject : Analytic.Eta24SameObject M A N
    coefficientReadout : DeltaCoefficientReadout

open DeltaAnalyticArithmeticSameObject public

sameObjectCoefficient9Recurrence :
  ∀ {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Analytic.WeightCompatibleNormalization M} →
  (same : DeltaAnalyticArithmeticSameObject M A N) →
  coefficientAt9 (coefficientReadout same)
  ≡ coefficientAt3 (coefficientReadout same)
      *ℤ coefficientAt3 (coefficientReadout same)
      -ℤ Tau.pow3Eleven
sameObjectCoefficient9Recurrence same =
  coefficient9HeckeRecurrence (coefficientReadout same)

sameObjectCoefficient27Recurrence :
  ∀ {M : Eisenstein.EisensteinAnalyticModel}
    {A : Disc.DiscriminantAlgebra M}
    {N : Analytic.WeightCompatibleNormalization M} →
  (same : DeltaAnalyticArithmeticSameObject M A N) →
  coefficientAt27 (coefficientReadout same)
  ≡
    (coefficientAt3 (coefficientReadout same)
      *ℤ coefficientAt3 (coefficientReadout same)
      *ℤ coefficientAt3 (coefficientReadout same))
      -ℤ
    ((+ 2 *ℤ Tau.pow3Eleven)
      *ℤ coefficientAt3 (coefficientReadout same))
sameObjectCoefficient27Recurrence same =
  coefficient27HeckeRecurrence (coefficientReadout same)

record DeltaAnalyticHeckeBoundary : Set where
  field
    analyticWeight12TransportDerived : Bool
    concreteTauRecurrencesReused : Bool
    sameObjectReadoutTransportsRecurrence : Bool
    qExpansionCoefficientExtractorConstructed : Bool
    eta24CoefficientIdentificationConstructed : Bool

canonicalDeltaAnalyticHeckeBoundary : DeltaAnalyticHeckeBoundary
canonicalDeltaAnalyticHeckeBoundary = record
  { analyticWeight12TransportDerived = true
  ; concreteTauRecurrencesReused = true
  ; sameObjectReadoutTransportsRecurrence = true
  ; qExpansionCoefficientExtractorConstructed = false
  ; eta24CoefficientIdentificationConstructed = false
  }
