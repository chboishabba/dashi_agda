module DASHI.Core.RelationalityGradeSeparationExact where

------------------------------------------------------------------------
-- RELATIONALITY GRADES: DO NOT PROMOTE "RELATIONAL" AS ONE PREDICATE
--
-- MATHEMATICAL / INTERNAL PROVENANCE
--
-- Roger A. Horn and Charles R. Johnson, Matrix Analysis, 2nd ed., Cambridge
-- University Press, 2013. DOI 10.1017/CBO9781139020411.  Background only for
-- rank/separability language.
--
-- David Blackwell, "Equivalent Comparisons of Experiments", Annals of
-- Mathematical Statistics 24(2), 1953. DOI 10.1214/aoms/1177729032.
-- Background only for observer/information comparison language.
--
-- Internal theorem-pattern provenance:
--   PR #621/#622 -> pair-valued syntax != genuine nonseparable interaction;
--   PR #606      -> history/body-conditioned reachability;
--   PR #618/#620 -> ecology/observer-conditioned realized outcomes.
--
-- The grade carrier below is DASHI bookkeeping for proof obligations, not a
-- historical taxonomy attributed to either mathematical source.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

------------------------------------------------------------------------
-- Increasing requirements.  A higher constructor names extra structure that
-- must be proved; it does not assert that every lower layer is empirically
-- present in every application.
------------------------------------------------------------------------

data RelationalityGrade : Set where
  endpointOnly
  pairValued
  endpointNonseparable
  historyConditioned
  observerContextConditioned
  : RelationalityGrade

hasPairCoordinate : RelationalityGrade → Bool
hasPairCoordinate endpointOnly = false
hasPairCoordinate _ = true

requiresNonseparabilityWitness : RelationalityGrade → Bool
requiresNonseparabilityWitness endpointOnly = false
requiresNonseparabilityWitness pairValued = false
requiresNonseparabilityWitness _ = true

requiresHistoryCoordinate : RelationalityGrade → Bool
requiresHistoryCoordinate endpointOnly = false
requiresHistoryCoordinate pairValued = false
requiresHistoryCoordinate endpointNonseparable = false
requiresHistoryCoordinate historyConditioned = true
requiresHistoryCoordinate observerContextConditioned = true

requiresObserverOrContextCoordinate : RelationalityGrade → Bool
requiresObserverOrContextCoordinate observerContextConditioned = true
requiresObserverOrContextCoordinate _ = false

pairValuedDoesNotRequireNonseparability :
  requiresNonseparabilityWitness pairValued ≡ false
pairValuedDoesNotRequireNonseparability = refl

nonseparableDoesNotRequireHistory :
  requiresHistoryCoordinate endpointNonseparable ≡ false
nonseparableDoesNotRequireHistory = refl

historyConditionedDoesNotRequireObserverContext :
  requiresObserverOrContextCoordinate historyConditioned ≡ false
historyConditionedDoesNotRequireObserverContext = refl

observerContextIsStrictlyAdditionalRequirement :
  requiresHistoryCoordinate observerContextConditioned ≡ true
  × requiresObserverOrContextCoordinate observerContextConditioned ≡ true
observerContextIsStrictlyAdditionalRequirement = refl , refl

------------------------------------------------------------------------
-- Exact pair-valued-but-separable regression.
------------------------------------------------------------------------

data Bit : Set where
  bit0 bit1 : Bit

bitNat : Bit → Nat
bitNat bit0 = 0
bitNat bit1 = 1

additivePairResponse : Bit → Bit → Nat
additivePairResponse left right = bitNat left + bitNat right

pairSurfaceReallyUsesTwoArguments :
  additivePairResponse bit0 bit0 ≡ 0
  × additivePairResponse bit1 bit0 ≡ 1
pairSurfaceReallyUsesTwoArguments = refl , refl

record RelationalityGradeBoundary : Set where
  constructor relationality-grade-boundary
  field
    twoArgumentsProveNonseparability : Bool
    twoArgumentsProveNonseparabilityIsFalse :
      twoArgumentsProveNonseparability ≡ false
    nonseparabilityProvesHistoryDependence : Bool
    nonseparabilityProvesHistoryDependenceIsFalse :
      nonseparabilityProvesHistoryDependence ≡ false
    historyDependenceProvesObserverDependence : Bool
    historyDependenceProvesObserverDependenceIsFalse :
      historyDependenceProvesObserverDependence ≡ false
    observerDependenceProvesNormativeAuthority : Bool
    observerDependenceProvesNormativeAuthorityIsFalse :
      observerDependenceProvesNormativeAuthority ≡ false
    higherGradeProvesEmpiricalCausation : Bool
    higherGradeProvesEmpiricalCausationIsFalse :
      higherGradeProvesEmpiricalCausation ≡ false

canonicalRelationalityGradeBoundary : RelationalityGradeBoundary
canonicalRelationalityGradeBoundary =
  relationality-grade-boundary
    false refl false refl false refl false refl false refl
