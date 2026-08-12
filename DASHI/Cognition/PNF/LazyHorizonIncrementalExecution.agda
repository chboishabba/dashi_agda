module DASHI.Cognition.PNF.LazyHorizonIncrementalExecution where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.List.Base using (List)

open import DASHI.Cognition.PNF.NumericAuthority

------------------------------------------------------------------------
-- H3/H6/H9 laziness.
--
-- Logical staging is not enough: the expensive evidence producer for the next
-- horizon should receive only the unresolved residual from the previous one.
------------------------------------------------------------------------

record LazyHorizonSchedule : Set where
  constructor lazyHorizonSchedule
  field
    h3Input : List DemandId
    h3Unresolved : List DemandId
    h6Input : List DemandId
    h6Unresolved : List DemandId
    h9Input : List DemandId
    h6ConsumesExactlyH3Residual : h6Input ≡ h3Unresolved
    h9ConsumesExactlyH6Residual : h9Input ≡ h6Unresolved

open LazyHorizonSchedule public

------------------------------------------------------------------------
-- Reverse-dependency incremental frontier.
--
-- A new evidence/source observation wakes only its affected demand fibre and
-- downstream factor/projection dependants.  Whole-document/corpus rebuilding is
-- a recovery/audit operation, not the ordinary evidence-update semantics.
------------------------------------------------------------------------

record ReverseDependencyEdge : Set where
  constructor reverseDependencyEdge
  field
    sourceNumericId : Nat
    affectedDemand : DemandId

open ReverseDependencyEdge public

record IncrementalRecomputeReceipt : Set where
  constructor incrementalRecomputeReceipt
  field
    changedSourceIds : List Nat
    affectedDemandIds : List DemandId
    recomputedDemandIds : List DemandId
    recomputedExactlyAffected : recomputedDemandIds ≡ affectedDemandIds
    affectedFactorIds : List FactorId
    wholeDocumentRescan : Bool
    wholeDocumentRescanIsFalse : wholeDocumentRescan ≡ false
    wholeCorpusRescan : Bool
    wholeCorpusRescanIsFalse : wholeCorpusRescan ≡ false

open IncrementalRecomputeReceipt public

------------------------------------------------------------------------
-- Absence of evidence is not contradiction evidence.
------------------------------------------------------------------------

data NoEvidenceRefutationPermission : Set where

absenceOfEvidenceCannotRefute : NoEvidenceRefutationPermission → ⊥
absenceOfEvidenceCannotRefute ()

record LazyIncrementalBoundary : Set where
  constructor lazyIncrementalBoundary
  field
    h6GeneratedForSettledH3Demand : Bool
    h6GeneratedForSettledH3DemandIsFalse :
      h6GeneratedForSettledH3Demand ≡ false
    h9GeneratedForSettledH6Demand : Bool
    h9GeneratedForSettledH6DemandIsFalse :
      h9GeneratedForSettledH6Demand ≡ false
    ordinaryEvidenceUpdateRescansWholeCorpus : Bool
    ordinaryEvidenceUpdateRescansWholeCorpusIsFalse :
      ordinaryEvidenceUpdateRescansWholeCorpus ≡ false
    zeroEvidenceCountIsSemanticRefutation : Bool
    zeroEvidenceCountIsSemanticRefutationIsFalse :
      zeroEvidenceCountIsSemanticRefutation ≡ false

open LazyIncrementalBoundary public

canonicalLazyIncrementalBoundary : LazyIncrementalBoundary
canonicalLazyIncrementalBoundary =
  lazyIncrementalBoundary false refl false refl false refl false refl
