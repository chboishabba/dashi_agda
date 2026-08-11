module DASHI.Moonshine.Monster196884FibreInterferenceExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John H. Conway and Simon P. Norton,
-- "Monstrous Moonshine", Bulletin of the London Mathematical Society
-- 11 (1979), 308--339.
-- DOI: 10.1112/blms/11.3.308.
--
-- DASHI CONTRIBUTION
--
-- Prove the exact arithmetic refinement
--
--   196884 = (5 * 2) * 3^9 + (3 * 2) * 3^2
--          = 196830 + 54.
--
-- The factors are taken from the typed pointed-half-chart, Eisenstein phase,
-- and nine-address carriers.  The theorem is an arithmetic compatibility
-- with the existing C3 character evaluation.  It is not a decomposition or
-- construction of the Monster module V^natural_2.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.EisensteinNineRingInterferenceExact as Eisenstein
import DASHI.Biology.HalfChartNineRingQuotientExact as Half
import DASHI.Moonshine.Monster3BC3RepresentationRingEvaluationExact as C3

fineChartCount : Nat
fineChartCount = Half.unfoldedCount

finePhaseFieldCount : Nat
finePhaseFieldCount = Eisenstein.nineAddressFieldCount

fineSectorDimension : Nat
fineSectorDimension = fineChartCount * finePhaseFieldCount

coarsePhaseSymmetryCount : Nat
coarsePhaseSymmetryCount = Eisenstein.localPhaseSymmetryCount

coarseAddressCount : Nat
coarseAddressCount = 3 * 3

coarseSectorDimension : Nat
coarseSectorDimension = coarsePhaseSymmetryCount * coarseAddressCount

fibreInterferenceTotal : Nat
fibreInterferenceTotal = fineSectorDimension + coarseSectorDimension

fineChartCountIsTen : fineChartCount ≡ 10
fineChartCountIsTen = Half.unfoldedCountIsTen

finePhaseFieldCountIs19683 : finePhaseFieldCount ≡ 19683
finePhaseFieldCountIs19683 = Eisenstein.nineAddressFieldCountIs19683

fineSectorDimensionIs196830 : fineSectorDimension ≡ 196830
fineSectorDimensionIs196830 = refl

coarsePhaseSymmetryCountIsSix : coarsePhaseSymmetryCount ≡ 6
coarsePhaseSymmetryCountIsSix = Eisenstein.localPhaseSymmetryCountIsSix

coarseAddressCountIsNine : coarseAddressCount ≡ 9
coarseAddressCountIsNine = refl

coarseSectorDimensionIs54 : coarseSectorDimension ≡ 54
coarseSectorDimensionIs54 = refl

fibreInterferenceTotalIs196884 : fibreInterferenceTotal ≡ 196884
fibreInterferenceTotalIs196884 = refl

finePlusCoarseIdentity : 196830 + 54 ≡ 196884
finePlusCoarseIdentity = refl

factorizedIdentity :
  (5 * 2) * Eisenstein.nineAddressFieldCount
  + (3 * 2) * (3 * 3)
  ≡ 196884
factorizedIdentity = refl

matchesExistingMoonshineV2Dimension :
  fibreInterferenceTotal ≡ C3.moonshineV2Dimension
matchesExistingMoonshineV2Dimension = refl

coarseTermMatchesExisting3BTrace :
  coarseSectorDimension ≡ C3.moonshineV2TraceAt3B
coarseTermMatchesExisting3BTrace = refl

record Monster196884Boundary : Set where
  constructor monster196884Boundary
  field
    arithmeticIdentityExact : Bool
    arithmeticIdentityExactIsTrue : arithmeticIdentityExact ≡ true
    factorsConstructMonsterSubmodules : Bool
    factorsConstructMonsterSubmodulesIsFalse :
      factorsConstructMonsterSubmodules ≡ false
    equalityOfDimensionsGivesRepresentationIsomorphism : Bool
    equalityOfDimensionsGivesRepresentationIsomorphismIsFalse :
      equalityOfDimensionsGivesRepresentationIsomorphism ≡ false
    coefficientTenDerivedByThisIdentity : Bool
    coefficientTenDerivedByThisIdentityIsFalse :
      coefficientTenDerivedByThisIdentity ≡ false
    coarseTermEqualsCertified3BTraceNumerically : Bool
    coarseTermEqualsCertified3BTraceNumericallyIsTrue :
      coarseTermEqualsCertified3BTraceNumerically ≡ true

canonicalMonster196884Boundary : Monster196884Boundary
canonicalMonster196884Boundary =
  monster196884Boundary true refl false refl false refl false refl true refl
