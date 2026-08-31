module DASHI.Culture.IntellectualReceptionTernaryParetoSituatedChoiceExact where

open import DASHI.Core.Prelude

import Base369 as Base
import DASHI.Culture.IntellectualReceptionSituatedInformationParetoPreorderExact as Pareto
import DASHI.Culture.IntellectualReceptionIntersectionalInformationGeometryExact as Info
import DASHI.Core.ObserverIncomparabilityTypedJoinExact as ObserverJoin
import DASHI.Reasoning.TernaryComparisonSynthesisExact as Ternary
import DASHI.Governance.SexedHistoricalSubjectDialecticBidiExact as Dialectic

------------------------------------------------------------------------
-- 1. Strict Pareto improvement is proof-relevant and directional.
------------------------------------------------------------------------

record StrictParetoImproves
    (better worse : Pareto.SituatedInformationProfile) : Set where
  constructor strict-pareto-improves
  field
    worseBelowBetter : Pareto.ParetoNoWorse worse better
    betterNotBelowWorse : Pareto.ParetoNoWorse better worse → ⊥

open StrictParetoImproves public

allWeakProfile : Pareto.SituatedInformationProfile
allWeakProfile =
  Pareto.situated-information-profile
    Pareto.weak Pareto.weak Pareto.weak Pareto.weak Pareto.weak Pareto.weak

allStrongProfile : Pareto.SituatedInformationProfile
allStrongProfile =
  Pareto.situated-information-profile
    Pareto.strong Pareto.strong Pareto.strong Pareto.strong Pareto.strong Pareto.strong

allWeakBelowAllStrong : Pareto.ParetoNoWorse allWeakProfile allStrongProfile
allWeakBelowAllStrong =
  Pareto.pareto-no-worse
    Pareto.weak-strong Pareto.weak-strong Pareto.weak-strong
    Pareto.weak-strong Pareto.weak-strong Pareto.weak-strong

allStrongNotBelowAllWeak : Pareto.ParetoNoWorse allStrongProfile allWeakProfile → ⊥
allStrongNotBelowAllWeak witness =
  Pareto.strongNotAtMostWeak (Pareto.supportOrder witness)

allStrongStrictlyImprovesAllWeak : StrictParetoImproves allStrongProfile allWeakProfile
allStrongStrictlyImprovesAllWeak =
  strict-pareto-improves allWeakBelowAllStrong allStrongNotBelowAllWeak

------------------------------------------------------------------------
-- 2. Three-way proof-carrying situated comparison.
--
-- This is intentionally not a total decision procedure. A receipt must carry
-- evidence for strict left improvement, strict right improvement, or genuine
-- Pareto incomparability.
------------------------------------------------------------------------

data SituatedParetoRelation
    (left right : Pareto.SituatedInformationProfile) : Set where
  leftStrictlyImproves :
    StrictParetoImproves left right →
    SituatedParetoRelation left right

  rightStrictlyImproves :
    StrictParetoImproves right left →
    SituatedParetoRelation left right

  paretoIncomparable :
    Pareto.ParetoIncomparable left right →
    SituatedParetoRelation left right

allStrongVsAllWeak : SituatedParetoRelation allStrongProfile allWeakProfile
allStrongVsAllWeak = leftStrictlyImproves allStrongStrictlyImprovesAllWeak

allWeakVsAllStrong : SituatedParetoRelation allWeakProfile allStrongProfile
allWeakVsAllStrong = rightStrictlyImproves allStrongStrictlyImprovesAllWeak

discriminatorVsGoverned :
  SituatedParetoRelation Pareto.discriminatorProfile Pareto.governedProfile
discriminatorVsGoverned =
  paretoIncomparable Pareto.canonicalSituatedInformationIncomparability

------------------------------------------------------------------------
-- 3. Base369 ternary encoding is an explicit comparison policy.
--
-- tri-high = left strictly improves
-- tri-low  = right strictly improves
-- tri-mid  = incomparable
--
-- This does NOT identify Pareto incomparability with epistemic uncertainty,
-- neutrality, mediation, or dialectical synthesis.
------------------------------------------------------------------------

relationCode :
  ∀ {left right} →
  SituatedParetoRelation left right →
  Base.TriTruth
relationCode (leftStrictlyImproves evidence) = Base.tri-high
relationCode (rightStrictlyImproves evidence) = Base.tri-low
relationCode (paretoIncomparable evidence) = Base.tri-mid

strongWeakCodeIsHigh : relationCode allStrongVsAllWeak ≡ Base.tri-high
strongWeakCodeIsHigh = refl

weakStrongCodeIsLow : relationCode allWeakVsAllStrong ≡ Base.tri-low
weakStrongCodeIsLow = refl

crossedProfileCodeIsMid : relationCode discriminatorVsGoverned ≡ Base.tri-mid
crossedProfileCodeIsMid = refl

------------------------------------------------------------------------
-- 4. The 3-way result can enter the existing 9/27 comparison-synthesis carrier
-- without losing the original comparison boundary.
------------------------------------------------------------------------

opposedParetoComparison : Ternary.Comparison9
opposedParetoComparison =
  relationCode allStrongVsAllWeak , relationCode allWeakVsAllStrong

paretoSynthesisChoice : Ternary.SynthesisChoice27
paretoSynthesisChoice =
  Ternary.makeSynthesisChoice
    (relationCode allStrongVsAllWeak)
    (relationCode allWeakVsAllStrong)
    (relationCode discriminatorVsGoverned)

paretoSynthesisRetainsComparison :
  Ternary.comparisonOfSynthesis paretoSynthesisChoice ≡ opposedParetoComparison
paretoSynthesisRetainsComparison = refl

paretoSynthesisRetainsIncomparabilityCoordinate :
  Ternary.synthesisCoordinate paretoSynthesisChoice ≡ Base.tri-mid
paretoSynthesisRetainsIncomparabilityCoordinate = refl

------------------------------------------------------------------------
-- 5. Far x-pollination: support and provenance are themselves incomparable
-- observers on the finite situated-information carrier.
------------------------------------------------------------------------

supportProvenanceIncomparableObservers :
  ObserverJoin.IncomparableObservers Info.supportClass Info.provenanceClass
supportProvenanceIncomparableObservers =
  ObserverJoin.incomparableObservers
    Info.authorityInherited
    Info.authorityIntroduced
    refl
    (λ ())
    Info.presentFutureInherited
    Info.authorityInherited
    refl
    (λ ())

supportDoesNotRefineProvenance :
  DASHI.Core.ObserverRefinementLatticeExact.Refines
    Info.provenanceClass Info.supportClass → ⊥
supportDoesNotRefineProvenance =
  ObserverJoin.leftDoesNotRefineRight supportProvenanceIncomparableObservers

provenanceDoesNotRefineSupport :
  DASHI.Core.ObserverRefinementLatticeExact.Refines
    Info.supportClass Info.provenanceClass → ⊥
provenanceDoesNotRefineSupport =
  ObserverJoin.rightDoesNotRefineLeft supportProvenanceIncomparableObservers

supportProvenanceJointStrictlyRefinesSupport :
  DASHI.Core.ObserverRefinementLatticeExact.StrictRefinement
    Info.supportClass
    (DASHI.Core.ObserverRefinementLatticeExact.pairObserver
      Info.supportClass Info.provenanceClass)
supportProvenanceJointStrictlyRefinesSupport =
  ObserverJoin.jointStrictlyRefinesLeft supportProvenanceIncomparableObservers

supportProvenanceJointStrictlyRefinesProvenance :
  DASHI.Core.ObserverRefinementLatticeExact.StrictRefinement
    Info.provenanceClass
    (DASHI.Core.ObserverRefinementLatticeExact.pairObserver
      Info.supportClass Info.provenanceClass)
supportProvenanceJointStrictlyRefinesProvenance =
  ObserverJoin.jointStrictlyRefinesRight supportProvenanceIncomparableObservers

supportProvenanceLeastTypedJoin :
  ObserverJoin.LeastTypedObservationJoin Info.supportClass Info.provenanceClass
supportProvenanceLeastTypedJoin =
  ObserverJoin.canonicalLeastTypedObservationJoin
    Info.supportClass Info.provenanceClass

------------------------------------------------------------------------
-- 6. Dialectic and ternary boundaries stay explicit.
------------------------------------------------------------------------

data ParetoIncomparableMeansEpistemicUnresolved : Set where
data ParetoIncomparableMeansDialecticMediator : Set where
data ParetoIncomparableGuaranteesSynthesis : Set where
data TernaryCodeMakesParetoTotal : Set where
data TypedObservationJoinAuthorisesSemanticPooling : Set where

incomparabilityDoesNotMeanEpistemicUnresolved :
  ParetoIncomparableMeansEpistemicUnresolved → ⊥
incomparabilityDoesNotMeanEpistemicUnresolved ()

incomparabilityDoesNotMeanDialecticMediator :
  ParetoIncomparableMeansDialecticMediator → ⊥
incomparabilityDoesNotMeanDialecticMediator ()

incomparabilityDoesNotGuaranteeSynthesis :
  ParetoIncomparableGuaranteesSynthesis → ⊥
incomparabilityDoesNotGuaranteeSynthesis ()

ternaryEncodingDoesNotMakeParetoTotal : TernaryCodeMakesParetoTotal → ⊥
ternaryEncodingDoesNotMakeParetoTotal ()

typedJoinDoesNotAuthoriseSemanticPooling :
  TypedObservationJoinAuthorisesSemanticPooling → ⊥
typedJoinDoesNotAuthoriseSemanticPooling ()

historicalCounterFormationStillDoesNotGuaranteeSynthesis :
  Dialectic.CounterFormationGuaranteesSynthesis → ⊥
historicalCounterFormationStillDoesNotGuaranteeSynthesis =
  Dialectic.counterFormationDoesNotGuaranteeSynthesis

record IntellectualReceptionTernaryParetoSituatedChoiceBoundary : Set where
  constructor intellectual-reception-ternary-pareto-situated-choice-boundary
  field
    strictLeftImprovementConstructed : Bool
    strictRightImprovementConstructed : Bool
    incomparableOutcomeConstructed : Bool
    ternaryEncodingIsExplicitPolicy : Bool
    synthesisRetainsComparisonBoundary : Bool
    supportAndProvenanceObserversAreIncomparable : Bool
    typedJoinStrictlyRefinesBoth : Bool
    paretoIncomparabilityMeansEpistemicUnresolved : Bool
    paretoIncomparabilityMeansDialecticMediator : Bool
    paretoIncomparabilityGuaranteesSynthesis : Bool
    ternaryEncodingMakesPartialOrderTotal : Bool
    typedJoinAuthorisesSemanticPooling : Bool
    sourceAttributionBoundarySurvives : Bool

canonicalIntellectualReceptionTernaryParetoSituatedChoiceBoundary :
  IntellectualReceptionTernaryParetoSituatedChoiceBoundary
canonicalIntellectualReceptionTernaryParetoSituatedChoiceBoundary =
  intellectual-reception-ternary-pareto-situated-choice-boundary
    true true true true true true true false false false false false true
