module DASHI.Governance.EffectiveChoiceConcentrationExact where

------------------------------------------------------------------------
-- EFFECTIVE CHOICE CONCENTRATION
--
-- This module inserts the missing layer between formal plurality and effective
-- monopoly.  A market/institution/political field can contain several formal
-- actors while only a smaller subset are practical substitutes for a given
-- subject and query.
--
-- The calculus is domain-neutral.  It does not infer competition-law market
-- power, coercion, political capture, collusion, or illegality from numerical
-- concentration alone.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Governance.EffectiveInstitutionalChoiceExact as Choice

------------------------------------------------------------------------
-- Distinct choice topologies.
------------------------------------------------------------------------

data ChoiceTopology : Set where
  pluralCompetitive concentratedPlural dominantPair effectiveMonopoly : ChoiceTopology

record EffectiveChoiceField : Set where
  constructor effectiveChoiceField
  field
    formalProviderCount : Nat
    effectiveSubstituteCount : Nat
    dominantProviderCount : Nat
    dominantSharePercent : Nat
    switchingCost : Nat
    dependency : Nat
    essentiality : Nat
    topology : ChoiceTopology

open EffectiveChoiceField public

------------------------------------------------------------------------
-- Concentration changes the outside-option geometry, not the semantic class of
-- every downstream act.
------------------------------------------------------------------------

data ConcentrationPromotesMonopoly : Set where

data DominantPairPromotesCoercion : Set where

data EffectiveMonopolyPromotesCoercion : Set where

data HighLeveragePromotesCoercion : Set where

concentrationDoesNotPromoteMonopoly : ConcentrationPromotesMonopoly → ⊥
concentrationDoesNotPromoteMonopoly ()

dominantPairDoesNotPromoteCoercion : DominantPairPromotesCoercion → ⊥
dominantPairDoesNotPromoteCoercion ()

effectiveMonopolyDoesNotPromoteCoercion : EffectiveMonopolyPromotesCoercion → ⊥
effectiveMonopolyDoesNotPromoteCoercion ()

highLeverageDoesNotPromoteCoercion : HighLeveragePromotesCoercion → ⊥
highLeverageDoesNotPromoteCoercion ()

------------------------------------------------------------------------
-- Coercive use remains a separate witness.  The point of concentration is that
-- it can reduce outside options and therefore change the practical leverage of
-- an independently evidenced act.
------------------------------------------------------------------------

record CoerciveUseWitness : Set where
  constructor coerciveUseWitness
  field
    refusalRestricted : Bool
    meaningfulPenalty : Bool
    outsideOptionScarcityUsedAsLeverage : Bool

open CoerciveUseWitness public

record ConcentratedDependencyEntrapmentCandidate : Set where
  constructor concentratedDependencyEntrapmentCandidate
  field
    field : EffectiveChoiceField
    lowEffectiveSubstitution : Bool
    dependencyMaterial : Bool
    coerciveUse : CoerciveUseWitness

------------------------------------------------------------------------
-- Observer-relative substitution.  The same institutional field may expose a
-- different outside-option set to consumers, suppliers, workers, students,
-- patients, or voters.
------------------------------------------------------------------------

data ChoiceObserver : Set where
  consumerObserver supplierObserver workerObserver studentObserver : ChoiceObserver
  patientObserver voterObserver regulatorObserver : ChoiceObserver

record ObserverChoiceProjection : Set where
  constructor observerChoiceProjection
  field
    observer : ChoiceObserver
    visibleFormalOptions : Nat
    usableSubstitutes : Nat

open ObserverChoiceProjection public

data OneObserverProjectionPromotesWholeSystem : Set where

oneObserverDoesNotPromoteWholeSystem : OneObserverProjectionPromotesWholeSystem → ⊥
oneObserverDoesNotPromoteWholeSystem ()

------------------------------------------------------------------------
-- Connection to existing institutional-choice theorem.
------------------------------------------------------------------------

formalPluralityStillDoesNotPromoteEffectivePlurality :
  Choice.FormalPluralityPromotesEffectivePlurality → ⊥
formalPluralityStillDoesNotPromoteEffectivePlurality =
  Choice.formalPluralityDoesNotPromoteEffectivePlurality

record EffectiveChoiceConcentrationBoundary : Set where
  constructor effectiveChoiceConcentrationBoundary
  field
    formalPluralityEqualsEffectiveSubstitutability : Bool
    dominantPairEqualsMonopoly : Bool
    dominantPairEqualsCoercion : Bool
    monopolyEqualsCoercion : Bool
    concentrationCanReduceOutsideOptions : Bool
    coerciveUseRequiresSeparateWitness : Bool
    observerRelativeChoiceCanDiffer : Bool

canonicalEffectiveChoiceConcentrationBoundary :
  EffectiveChoiceConcentrationBoundary
canonicalEffectiveChoiceConcentrationBoundary =
  effectiveChoiceConcentrationBoundary false false false false true true true
