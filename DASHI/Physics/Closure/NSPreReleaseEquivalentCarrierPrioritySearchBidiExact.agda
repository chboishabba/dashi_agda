module DASHI.Physics.Closure.NSPreReleaseEquivalentCarrierPrioritySearchBidiExact where

------------------------------------------------------------------------
-- PRE-RELEASE EQUIVALENT-CARRIER PRIORITY SEARCH
--
-- This owner records the stronger archaeology result obtained after refusing
-- to equate `Closed = false` with mathematical falsity.
--
-- The pre-release NS programme repeatedly moved an already-existing analytic
-- object through progressively more literal carriers:
--
--   R353 signed Gram family
--      -> R372 Round104 critical-production compiler
--      -> R375 physical companion/integration
--      -> R377 physical core
--      -> R379 literal global Gram debt
--      -> R395 literal temporal R378 payment
--      -> R406 fixed live output carrier
--      -> R414/R421 critical barrier
--      -> R507 old Round104 slice -> literal R406 slice by one same-object weld.
--
-- Therefore failure to find an inhabitant under the *newest* R406 record name
-- is not enough to conclude that the mathematical estimate did not exist in an
-- older equivalent carrier.  Priority search must inspect equivalent-carrier
-- producers before making that inference.
--
-- The surviving exact distinction is:
--
--   old analytic producer present
--     != old producer proved same object as literal R406 target
--     != kernel receipt for the final composition.
--
-- This module does not assert historical priority.  It narrows the next search
-- to the missing same-object/producer coordinates instead of treating status
-- booleans as theorem negations.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Physics.Closure.NSTriadKNRound104ToLiteralR406CriticalSliceRound507Exact as R507
import DASHI.Physics.Closure.NSTriadKNQuadraticCompanionSignedHeatToBarrierRound423Exact as R423
import DASHI.Physics.Closure.NSTriadKNHeatWeightedNestedCotlarSteinRound350Exact as R350

------------------------------------------------------------------------
-- 1. Search state is indexed by representation level.
------------------------------------------------------------------------

data HistoricalCarrier : Set where
  r353SignedGramFamily : HistoricalCarrier
  round104CriticalProduction : HistoricalCarrier
  physicalSignedGramFamily : HistoricalCarrier
  literalGlobalGramDebt : HistoricalCarrier
  literalTemporalR378Payment : HistoricalCarrier
  literalR406Remainder : HistoricalCarrier
  quadraticCompanionHeatCross : HistoricalCarrier

data ArchaeologyCoordinate : Set where
  analyticProducerTerm : ArchaeologyCoordinate
  sameObjectWeldToR406 : ArchaeologyCoordinate
  cutoffUniformPhysicalBudget : ArchaeologyCoordinate
  temporalFTCRealization : ArchaeologyCoordinate
  criticalInitialCeiling : ArchaeologyCoordinate
  finalKernelReceipt : ArchaeologyCoordinate

data SearchAnswer : Set where
  located : SearchAnswer
  notYetLocated : SearchAnswer
  statusOnlyNotDecisive : SearchAnswer

record HistoricalSearchCell : Set where
  constructor historical-search-cell
  field
    carrier : HistoricalCarrier
    coordinate : ArchaeologyCoordinate
    answer : SearchAnswer

open HistoricalSearchCell public

------------------------------------------------------------------------
-- 2. What the surviving source already proves about representation reuse.
------------------------------------------------------------------------

round104ToR406CoordinatesAlreadyMatch : Bool
round104ToR406CoordinatesAlreadyMatch =
  R507.round507Round104AndR414SliceCoordinatesAlreadyMatch

onlyExtraCriticalSliceReceiptIsR406RemainderEquality : Bool
onlyExtraCriticalSliceReceiptIsR406RemainderEquality =
  R507.round507OnlyAdditionalRepresentationReceiptIsR406RemainderEquality

schurRouteAlreadyKnownSufficient : Bool
schurRouteAlreadyKnownSufficient =
  R423.round423SchurCriticalRouteIsSufficientProducer

schurRouteNotNecessary : Bool
schurRouteNotNecessary =
  R423.round423SchurCriticalRouteIsNecessaryProducer

leanHeatSpacetimeCompilerReturned : Bool
leanHeatSpacetimeCompilerReturned =
  R350.round350HeatSpacetimeIntegrationClosedInLean

leanResolventConsumerReturned : Bool
leanResolventConsumerReturned =
  R350.round350ResolventGramConsumptionClosedInLean

round104ToR406CoordinatesAlreadyMatchIsTrue :
  round104ToR406CoordinatesAlreadyMatch ≡ true
round104ToR406CoordinatesAlreadyMatchIsTrue =
  R507.round507Round104AndR414SliceCoordinatesAlreadyMatchIsTrue

onlyExtraCriticalSliceReceiptIsR406RemainderEqualityIsTrue :
  onlyExtraCriticalSliceReceiptIsR406RemainderEquality ≡ true
onlyExtraCriticalSliceReceiptIsR406RemainderEqualityIsTrue =
  R507.round507OnlyAdditionalRepresentationReceiptIsR406RemainderEqualityIsTrue

schurRouteAlreadyKnownSufficientIsTrue : schurRouteAlreadyKnownSufficient ≡ true
schurRouteAlreadyKnownSufficientIsTrue =
  R423.round423SchurCriticalRouteIsSufficientProducerIsTrue

schurRouteNotNecessaryIsFalse : schurRouteNotNecessary ≡ false
schurRouteNotNecessaryIsFalse =
  R423.round423SchurCriticalRouteIsNecessaryProducerIsFalse

leanHeatSpacetimeCompilerReturnedIsTrue :
  leanHeatSpacetimeCompilerReturned ≡ true
leanHeatSpacetimeCompilerReturnedIsTrue =
  R350.round350HeatSpacetimeIntegrationClosedInLeanIsTrue

leanResolventConsumerReturnedIsTrue :
  leanResolventConsumerReturned ≡ true
leanResolventConsumerReturnedIsTrue =
  R350.round350ResolventGramConsumptionClosedInLeanIsTrue

------------------------------------------------------------------------
-- 3. Search interpretation.
------------------------------------------------------------------------

-- We have located compiler/representation terms in the older lanes.  What is
-- not yet located is a source term that simultaneously supplies the literal
-- physical cutoff-uniform budget AND the final R406 same-object weld.

olderCarrierCompilerLocated : HistoricalSearchCell
olderCarrierCompilerLocated =
  historical-search-cell round104CriticalProduction analyticProducerTerm located

r406SameObjectWeldSearch : HistoricalSearchCell
r406SameObjectWeldSearch =
  historical-search-cell literalR406Remainder sameObjectWeldToR406 notYetLocated

physicalBudgetSearch : HistoricalSearchCell
physicalBudgetSearch =
  historical-search-cell quadraticCompanionHeatCross cutoffUniformPhysicalBudget notYetLocated

kernelReceiptSearch : HistoricalSearchCell
kernelReceiptSearch =
  historical-search-cell literalR406Remainder finalKernelReceipt notYetLocated

------------------------------------------------------------------------
-- 4. Firewalls for priority reasoning.
------------------------------------------------------------------------

data NewNameAbsentImpliesOldProducerAbsentPermission : Set where
data StatusFalseImpliesNoSourceTermPermission : Set where
data OldProducerImpliesLiteralR406PaymentPermission : Set where
data CompilerReceiptImpliesHistoricalPriorityPermission : Set where

newNameAbsenceDoesNotEraseEquivalentCarrier :
  NewNameAbsentImpliesOldProducerAbsentPermission → ⊥
newNameAbsenceDoesNotEraseEquivalentCarrier ()

statusFalseDoesNotProveNoSourceTerm :
  StatusFalseImpliesNoSourceTermPermission → ⊥
statusFalseDoesNotProveNoSourceTerm ()

oldProducerNeedsSameObjectWeld :
  OldProducerImpliesLiteralR406PaymentPermission → ⊥
oldProducerNeedsSameObjectWeld ()

compilerReceiptDoesNotEstablishPriority :
  CompilerReceiptImpliesHistoricalPriorityPermission → ⊥
compilerReceiptDoesNotEstablishPriority ()

------------------------------------------------------------------------
-- 5. Highest-alpha next search.
------------------------------------------------------------------------

data NextPrioritySearch : Set where
  searchOlderGramSchurPhysicalProducer : NextPrioritySearch
  searchRound104PhysicalFamilyConstructor : NextPrioritySearch
  searchLiteralR406RemainderWeld : NextPrioritySearch
  searchTemporalFTCConcreteInstance : NextPrioritySearch
  searchFinalPreReleaseKernelComposition : NextPrioritySearch

highestAlphaPrioritySearch : NextPrioritySearch
highestAlphaPrioritySearch = searchOlderGramSchurPhysicalProducer

preReleasePriorityResolved : Bool
preReleasePriorityResolved = false

preReleaseEquivalentCarrierSearchStillLive : Bool
preReleaseEquivalentCarrierSearchStillLive = true

preReleasePriorityResolvedIsFalse : preReleasePriorityResolved ≡ false
preReleasePriorityResolvedIsFalse = refl

preReleaseEquivalentCarrierSearchStillLiveIsTrue :
  preReleaseEquivalentCarrierSearchStillLive ≡ true
preReleaseEquivalentCarrierSearchStillLiveIsTrue = refl
