module DASHI.Cognition.PNF.TSFVSemanticQueryFutureSplitExact where

------------------------------------------------------------------------
-- TSFV / PNF CONCRETE FUTURE-SPLIT REGRESSION
--
-- Reuses the existing two-world semantic-query fixture:
--
--   coarseIdentityQuery:
--     canonicalReferent      -> zer
--     impersonatorReferent   -> zer
--
--   provenanceQuery:
--     canonicalReferent      -> pos
--     impersonatorReferent   -> neg
--
-- We make "reveal the provenance query" a proof-bearing admissible action.
-- Both coarse-equal worlds execute the same action while preserving world
-- identity, after which their observations differ.  Hence they are not
-- FutureEquivalent for this action language.
--
-- This is a semantic/TSFV-PNF dynamic regression only.  It is NOT a physical
-- TSFV history-to-Candidate256 realization or a quantum-dynamics claim.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.List using ([]; _∷_)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.Unit using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Fin.Base using (Fin; zero; suc)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym)

import DASHI.Cognition.PNF.SemanticQueryResidualFibreSSSPBridgeExact as Query
import DASHI.Algebra.Trit as Trit
import DASHI.Core.TypedDependencyCore as Dependency
import DASHI.Core.AdmissibleReachability as Reachability
import DASHI.Core.FutureObservationalRefinement as Future
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Core.FutureSafeCoarseFibreCapacityExact as Capacity
import DASHI.Core.GeneralResidualFibreCardinalityExact as Cardinality
import DASHI.Core.ResidualFibreLowerBoundExact as Lower

------------------------------------------------------------------------
-- 1. Query/world dynamic state.
------------------------------------------------------------------------

QueryWorldState : Set
QueryWorldState = Query.ExampleQuery × Query.ExampleWorld

data QueryAction : Set where
  revealProvenance : QueryAction

Precondition : QueryWorldState -> QueryAction -> Set
Precondition (Query.coarseIdentityQuery , world) revealProvenance = ⊤
Precondition (Query.provenanceQuery , world) revealProvenance = ⊥

data Postcondition : QueryWorldState -> QueryAction -> QueryWorldState -> Set where
  revealCanonical :
    Postcondition
      (Query.coarseIdentityQuery , Query.canonicalReferent)
      revealProvenance
      (Query.provenanceQuery , Query.canonicalReferent)

  revealImpersonator :
    Postcondition
      (Query.coarseIdentityQuery , Query.impersonatorReferent)
      revealProvenance
      (Query.provenanceQuery , Query.impersonatorReferent)

semanticQueryActionSystem :
  Dependency.DependentActionSystem QueryWorldState QueryAction
semanticQueryActionSystem =
  record
    { Precondition = Precondition
    ; Postcondition = Postcondition
    ; actionLabel = λ { revealProvenance -> "reveal provenance query" }
    }

observeQueryWorld :
  QueryWorldState -> Trit.Trit
observeQueryWorld (query , world) =
  Query.exampleObserve query world

canonicalBefore : QueryWorldState
canonicalBefore =
  Query.coarseIdentityQuery , Query.canonicalReferent

impersonatorBefore : QueryWorldState
impersonatorBefore =
  Query.coarseIdentityQuery , Query.impersonatorReferent

canonicalAfter : QueryWorldState
canonicalAfter =
  Query.provenanceQuery , Query.canonicalReferent

impersonatorAfter : QueryWorldState
impersonatorAfter =
  Query.provenanceQuery , Query.impersonatorReferent

currentObservationsAgree :
  observeQueryWorld canonicalBefore
  ≡ observeQueryWorld impersonatorBefore
currentObservationsAgree =
  Query.coarseWorldsObservationEqual

------------------------------------------------------------------------
-- 2. Both worlds execute the same admissible reveal action.
------------------------------------------------------------------------

canonicalReveal :
  Dependency.AdmissibleAction
    semanticQueryActionSystem
    canonicalBefore
    revealProvenance
canonicalReveal =
  record
    { precondition = tt
    ; after = canonicalAfter
    ; postcondition = revealCanonical
    ; dependencyReceipt =
        "existing retained world; refine only the active query from coarse identity to provenance"
    }

impersonatorReveal :
  Dependency.AdmissibleAction
    semanticQueryActionSystem
    impersonatorBefore
    revealProvenance
impersonatorReveal =
  record
    { precondition = tt
    ; after = impersonatorAfter
    ; postcondition = revealImpersonator
    ; dependencyReceipt =
        "existing retained world; refine only the active query from coarse identity to provenance"
    }

canonicalRevealExecution :
  Reachability.Executes
    semanticQueryActionSystem
    (revealProvenance ∷ [])
    canonicalBefore
    canonicalAfter
canonicalRevealExecution =
  Reachability.executesCons canonicalReveal Reachability.executesNil

impersonatorRevealExecution :
  Reachability.Executes
    semanticQueryActionSystem
    (revealProvenance ∷ [])
    impersonatorBefore
    impersonatorAfter
impersonatorRevealExecution =
  Reachability.executesCons impersonatorReveal Reachability.executesNil

futureObservationsDiffer :
  observeQueryWorld canonicalAfter
  ≡ observeQueryWorld impersonatorAfter ->
  ⊥
futureObservationsDiffer =
  Query.provenanceWorldsSeparate

------------------------------------------------------------------------
-- 3. Exact terminalisation defect and FutureEquivalent refutation.
------------------------------------------------------------------------

canonicalQueryTerminalisationDefect :
  Dynamic.TerminalisationDefect
    semanticQueryActionSystem
    observeQueryWorld
canonicalQueryTerminalisationDefect =
  Dynamic.terminalisationDefect
    (revealProvenance ∷ [])
    canonicalBefore
    impersonatorBefore
    canonicalAfter
    impersonatorAfter
    currentObservationsAgree
    canonicalRevealExecution
    impersonatorRevealExecution
    futureObservationsDiffer

coarseQueryIsNotDynamicallySafe :
  Dynamic.DynamicConsumerSafety
    semanticQueryActionSystem
    observeQueryWorld ->
  ⊥
coarseQueryIsNotDynamicallySafe safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    canonicalQueryTerminalisationDefect

canonicalAndImpersonatorNotFutureEquivalent :
  Future.FutureEquivalent
    semanticQueryActionSystem
    observeQueryWorld
    canonicalBefore
    impersonatorBefore ->
  ⊥
canonicalAndImpersonatorNotFutureEquivalent future =
  futureObservationsDiffer
    (future canonicalRevealExecution impersonatorRevealExecution)

impersonatorAndCanonicalNotFutureEquivalent :
  Future.FutureEquivalent
    semanticQueryActionSystem
    observeQueryWorld
    impersonatorBefore
    canonicalBefore ->
  ⊥
impersonatorAndCanonicalNotFutureEquivalent future =
  futureObservationsDiffer
    (sym (future impersonatorRevealExecution canonicalRevealExecution))

------------------------------------------------------------------------
-- 4. Concrete two-class future-distinct fibre.
------------------------------------------------------------------------

twoWorldRepresentative : Fin 2 -> QueryWorldState
twoWorldRepresentative zero = canonicalBefore
twoWorldRepresentative (suc zero) = impersonatorBefore

twoWorldFutureEquivalentIndicesEqual :
  {left right : Fin 2} ->
  Future.FutureEquivalent
    semanticQueryActionSystem
    observeQueryWorld
    (twoWorldRepresentative left)
    (twoWorldRepresentative right) ->
  left ≡ right
twoWorldFutureEquivalentIndicesEqual {zero} {zero} future = refl
twoWorldFutureEquivalentIndicesEqual {zero} {suc zero} future =
  ⊥-elim (canonicalAndImpersonatorNotFutureEquivalent future)
twoWorldFutureEquivalentIndicesEqual {suc zero} {zero} future =
  ⊥-elim (impersonatorAndCanonicalNotFutureEquivalent future)
twoWorldFutureEquivalentIndicesEqual {suc zero} {suc zero} future = refl

canonicalTwoWorldFutureDistinctFibre :
  Capacity.CanonicalFiniteFutureDistinctFibre
    2
    semanticQueryActionSystem
    observeQueryWorld
canonicalTwoWorldFutureDistinctFibre =
  Cardinality.finiteFutureDistinctFibre
    twoWorldRepresentative
    Trit.zer
    (λ { zero -> refl ; (suc zero) -> refl })
    twoWorldFutureEquivalentIndicesEqual

------------------------------------------------------------------------
-- 5. Concrete capacity consequence.
------------------------------------------------------------------------

twoFutureClassesForceResidualInjection :
  {Residual : Set} ->
  {residual : QueryWorldState -> Residual} ->
  Capacity.FutureSafeResidual
    semanticQueryActionSystem
    observeQueryWorld
    residual ->
  Cardinality.Injective
    (λ index -> residual (twoWorldRepresentative index))
twoFutureClassesForceResidualInjection safe =
  Capacity.futureSafeResidualInjectsCanonicalFutureClasses
    safe
    canonicalTwoWorldFutureDistinctFibre

twoFutureClassesForceBitCapacity :
  {bits : Nat} ->
  {residual : QueryWorldState -> Cardinality.BitWords bits} ->
  Capacity.FutureSafeResidual
    semanticQueryActionSystem
    observeQueryWorld
    residual ->
  2 ≤ Cardinality.pow2 bits
twoFutureClassesForceBitCapacity safe =
  Capacity.futureSafeBitResidualCapacityBound
    safe
    canonicalTwoWorldFutureDistinctFibre

------------------------------------------------------------------------
-- 6. Promotion boundary.
------------------------------------------------------------------------

record TSFVSemanticQueryFutureSplitBoundary : Set where
  constructor tsfv-semantic-query-future-split-boundary
  field
    proofBearingActionSystemConstructed : Bool
    sameCurrentObservationProved : Bool
    commonAdmissibleTraceConstructed : Bool
    futureObservationSplitProved : Bool
    futureEquivalenceRefuted : Bool
    concreteTwoClassCapacityBoundInstantiated : Bool
    physicalTSFVRealizationConstructed : Bool
    physicalTSFVRealizationConstructedIsFalse :
      physicalTSFVRealizationConstructed ≡ false
    semanticQueryActionIsPhysicalTimeEvolution : Bool
    semanticQueryActionIsPhysicalTimeEvolutionIsFalse :
      semanticQueryActionIsPhysicalTimeEvolution ≡ false

canonicalTSFVSemanticQueryFutureSplitBoundary :
  TSFVSemanticQueryFutureSplitBoundary
canonicalTSFVSemanticQueryFutureSplitBoundary =
  tsfv-semantic-query-future-split-boundary
    true true true true true true
    false refl
    false refl
