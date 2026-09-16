module DASHI.Reasoning.PlatoSymposiumResidualDialecticMechanismExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.QueryFactorisationSufficiency as Query
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Adequacy
import DASHI.Core.RecursiveParetoFrontierLiftingExact as Pareto
import DASHI.Philosophy.AgonisticRelationalPluralism as Agonistic
import DASHI.Philosophy.PlatoSymposiumPhilosophyBridgeExact as Plato
import DASHI.Reasoning.DialecticalOppositionNonExplosionExact as Opposition
import DASHI.Reasoning.JMDAristotleSymposiumSourceAtlasExact as Source
import DASHI.Reasoning.PlatoSymposiumSnowballParetoIndexingExact as Indexing

------------------------------------------------------------------------
-- RESIDUAL JMD SYMPOSIUM DIALECTIC / MECHANISM CROSS-POLLINATION
--
-- Source ownership rule:
--   every theorem contract below is from the supplied JMD/meta-introspector
--   archive and therefore retains JMD source ownership/attribution.  The finite
--   DASHI FactorsThrough collisions are new DASHI bridge theorems motivated by
--   those source fixtures; they are NOT reattributed to Plato, JMD or Lean.
--
-- This owner deliberately does not create another dialectic, mechanism,
-- contextual-valuation, Pareto or projection-adequacy ontology.  It adds the
-- two residual consumer distinctions that were not already paid exactly:
--
--   conflict intensity !-> reconciliation possibility
--   observed effect   !-> means/mechanism
--
-- Pausanias context sensitivity and Republic selection-vs-validity are retained
-- as JMD source contracts but delegated to stronger existing DASHI owners.
------------------------------------------------------------------------

archiveOwner : String
archiveOwner = "James Michael DuPont (JMD / meta-introspector)"

archiveHash : String
archiveHash = Source.archiveSha256

eryximachusHostileReconcilableContract : Plato.LeanPhilosophyTheoremContract
eryximachusHostileReconcilableContract = Plato.mkJMDContract
  "RequestProject.SymposiumGaps"
  "Plato.EryximachusOpposites.KB.most_hostile_reconcilable"
  "within the supplied Eryximachus KB, a most-hostile pair is nonetheless reconcilable through the source-defined opposition/reconciliation axioms"

marsyasSameEffectDifferentMeansContract : Plato.LeanPhilosophyTheoremContract
marsyasSameEffectDifferentMeansContract = Plato.mkJMDContract
  "RequestProject.SymposiumAlcibiades"
  "Plato.AlcibiadesMarsyas.KB.same_effect_different_means"
  "Marsyas and Socrates share the source-defined bewitching effect while differing on instrument use"

pausaniasContextContract : Plato.LeanPhilosophyTheoremContract
pausaniasContextContract = Plato.mkJMDContract
  "RequestProject.SymposiumGapsII"
  "Plato.PausaniasTwoLaws.KB.noble_here_not_elsewhere"
  "the supplied Pausanias KB derives nobility in one situation and its failure in another"

republicSelectionValidityContract : Plato.LeanPhilosophyTheoremContract
republicSelectionValidityContract = Plato.mkJMDContract
  "RequestProject.RepublicCity"
  "Plato.Republic.City.Selection.selection_is_not_universal_validity"
  "soundness inside a source-selected domain does not establish the unrestricted universal demand"

------------------------------------------------------------------------
-- Canonical parents remain authoritative.
------------------------------------------------------------------------

existingContextualOppositionBoundary : Opposition.DialecticalOppositionBoundary
existingContextualOppositionBoundary = Opposition.canonicalDialecticalOppositionBoundary

existingAgonisticPluralismBoundary : Agonistic.AgonisticPluralismBoundary
existingAgonisticPluralismBoundary = Agonistic.canonicalAgonisticPluralismBoundary

existingProjectionAdequacyBoundary : Adequacy.QueryIndexedProjectionAdequacyBoundary
existingProjectionAdequacyBoundary = Adequacy.canonicalQueryIndexedProjectionAdequacyBoundary

existingRecursiveParetoBoundary : Pareto.RecursiveParetoFrontierBoundary
existingRecursiveParetoBoundary = Pareto.canonicalRecursiveParetoFrontierBoundary

existingIndexingBoundary : Indexing.PlatoSymposiumIndexingBoundary
existingIndexingBoundary = Indexing.canonicalPlatoSymposiumIndexingBoundary

------------------------------------------------------------------------
-- 1. Conflict intensity does not determine reconciliation possibility.
--
-- IMPORTANT ATTRIBUTION BOUNDARY:
-- The JMD Eryximachus source theorem proves reconciliation for the source KB's
-- most-hostile pairs.  The collision below is a DASHI generalisation: outside
-- that source KB, an equally intense opposition may or may not have a paid
-- reconciliation path.  Hence intensity alone is insufficient for the general
-- consumer query.
------------------------------------------------------------------------

data ConflictWorld : Set where
  intenseConflictWithReconciliationPath : ConflictWorld
  intenseConflictWithoutReconciliationPath : ConflictWorld

data ConflictIntensitySurface : Set where
  sameMaximalOpposition : ConflictIntensitySurface

data ReconciliationQuery : Set where
  reconciliationPossibilityQuestion : ReconciliationQuery

data ReconciliationAnswer : Set where
  reconciliationPathAvailable : ReconciliationAnswer
  reconciliationPathUnpaid : ReconciliationAnswer

conflictIntensityProjection : ConflictWorld → ConflictIntensitySurface
conflictIntensityProjection intenseConflictWithReconciliationPath = sameMaximalOpposition
conflictIntensityProjection intenseConflictWithoutReconciliationPath = sameMaximalOpposition

ReconciliationAnswerFor : ReconciliationQuery → Set
ReconciliationAnswerFor reconciliationPossibilityQuestion = ReconciliationAnswer

askReconciliation :
  (query : ReconciliationQuery) → ConflictWorld → ReconciliationAnswerFor query
askReconciliation reconciliationPossibilityQuestion intenseConflictWithReconciliationPath =
  reconciliationPathAvailable
askReconciliation reconciliationPossibilityQuestion intenseConflictWithoutReconciliationPath =
  reconciliationPathUnpaid

reconciliationQuestions : Query.InquiryQuestionFamily ConflictWorld ReconciliationQuery
reconciliationQuestions = Query.inquiryQuestionFamily ReconciliationAnswerFor askReconciliation

conflictIntensityDoesNotDetermineReconciliationPossibility :
  Query.FactorsThrough
    reconciliationQuestions
    conflictIntensityProjection
    reconciliationPossibilityQuestion → ⊥
conflictIntensityDoesNotDetermineReconciliationPossibility factor = helper first second
  where
    first :
      reconciliationPathAvailable ≡
      Query.quotientAnswer factor sameMaximalOpposition
    first = Query.factorisation factor intenseConflictWithReconciliationPath

    second :
      reconciliationPathUnpaid ≡
      Query.quotientAnswer factor sameMaximalOpposition
    second = Query.factorisation factor intenseConflictWithoutReconciliationPath

    helper :
      reconciliationPathAvailable ≡ Query.quotientAnswer factor sameMaximalOpposition →
      reconciliationPathUnpaid ≡ Query.quotientAnswer factor sameMaximalOpposition →
      ⊥
    helper refl ()

------------------------------------------------------------------------
-- 2. Same observed effect does not determine means/mechanism.
--
-- Here the JMD source itself supplies the motivating collision: both Marsyas
-- and Socrates satisfy Bewitches, while instrument use differs.  DASHI records
-- the general information-loss theorem without importing the Lean proof.
------------------------------------------------------------------------

data EffectWorld : Set where
  sameEffectInstrumentalMeans : EffectWorld
  sameEffectNonInstrumentalMeans : EffectWorld

data EffectSurface : Set where
  sameObservedEffect : EffectSurface

data MeansQuery : Set where
  operativeMeansQuestion : MeansQuery

data MeansAnswer : Set where
  instrumentMediatedMeans : MeansAnswer
  nonInstrumentalMeans : MeansAnswer

effectProjection : EffectWorld → EffectSurface
effectProjection sameEffectInstrumentalMeans = sameObservedEffect
effectProjection sameEffectNonInstrumentalMeans = sameObservedEffect

MeansAnswerFor : MeansQuery → Set
MeansAnswerFor operativeMeansQuestion = MeansAnswer

askMeans : (query : MeansQuery) → EffectWorld → MeansAnswerFor query
askMeans operativeMeansQuestion sameEffectInstrumentalMeans = instrumentMediatedMeans
askMeans operativeMeansQuestion sameEffectNonInstrumentalMeans = nonInstrumentalMeans

meansQuestions : Query.InquiryQuestionFamily EffectWorld MeansQuery
meansQuestions = Query.inquiryQuestionFamily MeansAnswerFor askMeans

observedEffectDoesNotDetermineMeans :
  Query.FactorsThrough meansQuestions effectProjection operativeMeansQuestion → ⊥
observedEffectDoesNotDetermineMeans factor = helper first second
  where
    first : instrumentMediatedMeans ≡ Query.quotientAnswer factor sameObservedEffect
    first = Query.factorisation factor sameEffectInstrumentalMeans

    second : nonInstrumentalMeans ≡ Query.quotientAnswer factor sameObservedEffect
    second = Query.factorisation factor sameEffectNonInstrumentalMeans

    helper :
      instrumentMediatedMeans ≡ Query.quotientAnswer factor sameObservedEffect →
      nonInstrumentalMeans ≡ Query.quotientAnswer factor sameObservedEffect → ⊥
    helper refl ()

------------------------------------------------------------------------
-- Reused source-shape parents: context and selected-domain validity.
------------------------------------------------------------------------

pausaniasContextAlreadyHasCanonicalDashiAnalogue : Bool
pausaniasContextAlreadyHasCanonicalDashiAnalogue = true

contextDifferenceStillNotLogicalContradiction :
  Opposition.contextDifferenceIsLogicalContradiction
    Opposition.canonicalDialecticalOppositionBoundary ≡ false
contextDifferenceStillNotLogicalContradiction = refl

projectionAdequacyStillQueryIndexed :
  Adequacy.adequacyRequiresQueryIndex
    Adequacy.canonicalQueryIndexedProjectionAdequacyBoundary ≡ true
projectionAdequacyStillQueryIndexed = refl

oneQueryAdequacyStillDoesNotImplyAllQueries :
  Adequacy.oneQueryAdequacyImpliesAllQueryAdequacy
    Adequacy.canonicalQueryIndexedProjectionAdequacyBoundary ≡ false
oneQueryAdequacyStillDoesNotImplyAllQueries = refl

paretoSelectionStillNotProofAuthority :
  Pareto.paretoFrontierRefinementCreatesProofAuthority
    Pareto.canonicalRecursiveParetoFrontierBoundary ≡ false
paretoSelectionStillNotProofAuthority = refl

------------------------------------------------------------------------
-- Cross-pollination boundary.
------------------------------------------------------------------------

record PlatoSymposiumResidualDialecticMechanismBoundary : Set where
  constructor plato-symposium-residual-dialectic-mechanism-boundary
  field
    allArchiveContractsOwnedByJMD : Bool
    leanSourceTheoremsImportedAsAgdaProofs : Bool
    conflictIntensityDeterminesReconciliation : Bool
    retainedConflictForcesIrreconcilability : Bool
    retainedConflictForcesSynthesis : Bool
    observedEffectDeterminesMeans : Bool
    contextualDifferenceCreatesLogicalContradiction : Bool
    selectedDomainSuccessCreatesUniversalValidity : Bool
    sourceFixtureMayMotivateDashiCollision : Bool
    canonicalDashiOwnersRemainAuthoritative : Bool

open PlatoSymposiumResidualDialecticMechanismBoundary public

canonicalPlatoSymposiumResidualDialecticMechanismBoundary :
  PlatoSymposiumResidualDialecticMechanismBoundary
canonicalPlatoSymposiumResidualDialecticMechanismBoundary =
  plato-symposium-residual-dialectic-mechanism-boundary
    true
    false
    false
    false
    false
    false
    false
    false
    true
    true

residualCrossPollinationSummary : String
residualCrossPollinationSummary =
  "All source contracts remain attributed to the JMD-owned archive. Eryximachus supplies a source-bounded hostile-yet-reconcilable fixture and Marsyas/Socrates supplies a same-effect/different-means fixture. DASHI independently proves that conflict intensity does not determine reconciliation possibility and observed effect does not determine means, while Pausanias context-sensitivity and Republic selection-vs-validity reuse canonical context and query-indexed projection adequacy boundaries."
