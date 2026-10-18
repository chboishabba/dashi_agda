module DASHI.Physics.Laws.EffectiveTheoryLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Physics.Laws.EffectiveLimitHierarchy as Hierarchy
import DASHI.Physics.Limits.PhysicsLimitCommutingSquare as Limit
import DASHI.Physics.Laws.WorldLawStateTheorySeparationExact as Separation
import DASHI.Core.TheoryUnderdeterminationExperimentExact as Under

------------------------------------------------------------------------
-- EFFECTIVE THEORY LINEAGE / RESTRICTED VALIDITY
--
-- Scientific succession is not encoded as a forced boolean replacement.
-- A prior theory may remain adequate on a declared regime through an exact,
-- approximate, or empirical-effective bridge while failing to identify the
-- later theory globally.
------------------------------------------------------------------------

data TheoryRelationStatus : Set where
  exactRecovery : TheoryRelationStatus
  controlledEffectiveRecovery : TheoryRelationStatus
  asymptoticRecovery : TheoryRelationStatus
  empiricalEffectiveAgreement : TheoryRelationStatus
  observationallyEquivalentHere : TheoryRelationStatus
  unresolvedRelation : TheoryRelationStatus
  refutedOnDeclaredTest : TheoryRelationStatus

record EffectiveTheoryLineage : Set₁ where
  constructor effective-theory-lineage
  field
    EarlierTheory : Set
    LaterTheory : Set
    Regime : Set
    earlierTheory : EarlierTheory
    laterTheory : LaterTheory
    validRegime : Regime → Set
    status : TheoryRelationStatus
    residualReference : String
    derivationReference : String
    empiricalReference : String

open EffectiveTheoryLineage public

data RestrictedAdequacyImpliesGlobalIdentityPermission : Set where
data SupersededImpliesUselessEverywherePermission : Set where
data NumericalAgreementImpliesDerivationPermission : Set where

restrictedAdequacyDoesNotIdentifyTheoriesGlobally :
  RestrictedAdequacyImpliesGlobalIdentityPermission → ⊥
restrictedAdequacyDoesNotIdentifyTheoriesGlobally ()

supersededTheoryNeedNotBeUselessEverywhere :
  SupersededImpliesUselessEverywherePermission → ⊥
supersededTheoryNeedNotBeUselessEverywhere ()

numericalAgreementDoesNotManufactureDerivation :
  NumericalAgreementImpliesDerivationPermission → ⊥
numericalAgreementDoesNotManufactureDerivation ()

------------------------------------------------------------------------
-- Physics limit owners already encode the proof obligations:
-- exact recovery -> exact commutation
-- effective recovery -> controlled residual
-- asymptotic recovery -> vanishing residual.
------------------------------------------------------------------------

record EffectiveTheoryPromotionBoundary : Set where
  constructor effective-theory-promotion-boundary
  field
    exactTheoryIdentityNeedsExactCommutation : Bool
    exactTheoryIdentityNeedsExactCommutationIsTrue :
      exactTheoryIdentityNeedsExactCommutation ≡ true
    effectiveRecoveryNeedsControlledResidual : Bool
    effectiveRecoveryNeedsControlledResidualIsTrue :
      effectiveRecoveryNeedsControlledResidual ≡ true
    asymptoticRecoveryNeedsVanishingResidual : Bool
    asymptoticRecoveryNeedsVanishingResidualIsTrue :
      asymptoticRecoveryNeedsVanishingResidual ≡ true
    empiricalAgreementAloneIsDerivation : Bool
    empiricalAgreementAloneIsDerivationIsFalse :
      empiricalAgreementAloneIsDerivation ≡ false
    restrictedValidityMeansGlobalTheoryIdentity : Bool
    restrictedValidityMeansGlobalTheoryIdentityIsFalse :
      restrictedValidityMeansGlobalTheoryIdentity ≡ false

open EffectiveTheoryPromotionBoundary public

canonicalEffectiveTheoryPromotionBoundary : EffectiveTheoryPromotionBoundary
canonicalEffectiveTheoryPromotionBoundary =
  effective-theory-promotion-boundary
    true refl
    true refl
    true refl
    false refl
    false refl

------------------------------------------------------------------------
-- Concrete lineage labels for the gravity intuition.
-- These are representational statuses, not claims that either formal theory is
-- definitionally identical to the world.
------------------------------------------------------------------------

data GravityRegime : Set where
  weakFieldLowSpeed : GravityRegime
  strongFieldRelativistic : GravityRegime

data NewtonTheory : Set where
  newtonTheory : NewtonTheory

data RelativityTheory : Set where
  relativityTheory : RelativityTheory

newtonAsRestrictedEffectiveLineage : EffectiveTheoryLineage
newtonAsRestrictedEffectiveLineage =
  effective-theory-lineage
    NewtonTheory
    RelativityTheory
    GravityRegime
    newtonTheory
    relativityTheory
    valid
    controlledEffectiveRecovery
    "Controlled residual required for quantitative effective recovery."
    "Derivation/limit bridge must be supplied; label agreement is insufficient."
    "Empirical adequacy is regime-indexed and distinct from derivation."
  where
    valid : GravityRegime → Set
    valid weakFieldLowSpeed = ⊤
    valid strongFieldRelativistic = ⊥

separationBoundary : Separation.TheoryRecoveryBoundary
separationBoundary = Separation.canonicalTheoryRecoveryBoundary

underdeterminationBoundary : Under.TheoryUnderdeterminationBoundary
underdeterminationBoundary = Under.canonicalTheoryUnderdeterminationBoundary

record EffectiveTheoryLineageBoundary : Set where
  constructor effective-theory-lineage-boundary
  field
    olderTheoryCanRemainUsefulOnRestrictedRegime : Bool
    olderTheoryCanRemainUsefulOnRestrictedRegimeIsTrue :
      olderTheoryCanRemainUsefulOnRestrictedRegime ≡ true
    newerTheoryAutomaticallyDeletesOlderTheory : Bool
    newerTheoryAutomaticallyDeletesOlderTheoryIsFalse :
      newerTheoryAutomaticallyDeletesOlderTheory ≡ false
    effectiveAgreementImpliesOntologicalIdentity : Bool
    effectiveAgreementImpliesOntologicalIdentityIsFalse :
      effectiveAgreementImpliesOntologicalIdentity ≡ false
    theoryLineageStatusIsSeparateFromWorldState : Bool
    theoryLineageStatusIsSeparateFromWorldStateIsTrue :
      theoryLineageStatusIsSeparateFromWorldState ≡ true

open EffectiveTheoryLineageBoundary public

canonicalEffectiveTheoryLineageBoundary : EffectiveTheoryLineageBoundary
canonicalEffectiveTheoryLineageBoundary =
  effective-theory-lineage-boundary true refl false refl false refl true refl
