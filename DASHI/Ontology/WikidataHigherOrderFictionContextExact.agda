module DASHI.Ontology.WikidataHigherOrderFictionContextExact where

------------------------------------------------------------------------
-- HIGHER-ORDER CLASS / FICTION / CONTEXT FACTORISATION
--
-- Wikidata's class-order documentation defines a second-order class by the
-- order of its instances: its instances are first-order classes.  That is an
-- order-of-predication coordinate.  It does not by itself answer whether the
-- class is editorially about fiction, exists only inside a fictional world,
-- is an ordinary real-world modelling class, or is even applicable at the
-- current inspection level.
--
-- This module keeps those coordinates orthogonal.  The phrase
-- "fictional second-order class" is therefore represented as a lossy public
-- label over a richer fibre, not as one primitive semantic atom.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ArgumentLevelTransportHyperformalismExact as Level

------------------------------------------------------------------------
-- Independent coordinates.
------------------------------------------------------------------------

data ClassOrder : Set where
  firstOrder : ClassOrder
  secondOrder : ClassOrder
  thirdOrder : ClassOrder
  variableOrder : ClassOrder

data NarrativeDomain : Set where
  ordinaryModellingDomain : NarrativeDomain
  editoriallyAboutFiction : NarrativeDomain
  inWorldFictionalDomain : NarrativeDomain
  unspecifiedNarrativeDomain : NarrativeDomain

record HigherOrderClassState : Set where
  constructor higherOrderClassState
  field
    publicLabel : String
    classOrder : ClassOrder
    narrativeDomain : NarrativeDomain
    applicability : Level.Applicability
    provenanceNote : String

open HigherOrderClassState public

------------------------------------------------------------------------
-- Two semantically distinct fine states can occupy the same public label/order.
------------------------------------------------------------------------

editorialSecondOrderState : HigherOrderClassState
editorialSecondOrderState =
  higherOrderClassState
    "fictional second-order class"
    secondOrder
    editoriallyAboutFiction
    Level.applicableHere
    "editorial/metamodel classification about fictional first-order classes"

inWorldSecondOrderState : HigherOrderClassState
inWorldSecondOrderState =
  higherOrderClassState
    "fictional second-order class"
    secondOrder
    inWorldFictionalDomain
    Level.outsideCurrentComparisonScope
    "countermodel: second-order classification interpreted inside a fictional world"

samePublicLabel :
  publicLabel editorialSecondOrderState ≡ publicLabel inWorldSecondOrderState
samePublicLabel = refl

sameClassOrder :
  classOrder editorialSecondOrderState ≡ classOrder inWorldSecondOrderState
sameClassOrder = refl

narrativeDomainsDiffer :
  editoriallyAboutFiction ≡ inWorldFictionalDomain → ⊥
narrativeDomainsDiffer ()

applicabilityDiffers :
  Level.applicableHere ≡ Level.outsideCurrentComparisonScope → ⊥
applicabilityDiffers ()

------------------------------------------------------------------------
-- A class-order-only or label-only decoder cannot recover narrative domain.
------------------------------------------------------------------------

record OrderOnlyNarrativeDecoder : Set where
  constructor orderOnlyNarrativeDecoder
  field
    decodeNarrativeFromOrder : ClassOrder → NarrativeDomain
    editorialCorrect :
      decodeNarrativeFromOrder (classOrder editorialSecondOrderState)
      ≡ editoriallyAboutFiction
    inWorldCorrect :
      decodeNarrativeFromOrder (classOrder inWorldSecondOrderState)
      ≡ inWorldFictionalDomain

open OrderOnlyNarrativeDecoder public

classOrderCannotDetermineNarrativeDomain :
  OrderOnlyNarrativeDecoder → ⊥
classOrderCannotDetermineNarrativeDomain decoder =
  narrativeDomainsDiffer
    (trans
      (sym (editorialCorrect decoder))
      (trans
        (cong (decodeNarrativeFromOrder decoder) sameClassOrder)
        (inWorldCorrect decoder)))

record LabelOnlyNarrativeDecoder : Set where
  constructor labelOnlyNarrativeDecoder
  field
    decodeNarrativeFromLabel : String → NarrativeDomain
    editorialLabelCorrect :
      decodeNarrativeFromLabel (publicLabel editorialSecondOrderState)
      ≡ editoriallyAboutFiction
    inWorldLabelCorrect :
      decodeNarrativeFromLabel (publicLabel inWorldSecondOrderState)
      ≡ inWorldFictionalDomain

open LabelOnlyNarrativeDecoder public

publicLabelCannotDetermineNarrativeDomain :
  LabelOnlyNarrativeDecoder → ⊥
publicLabelCannotDetermineNarrativeDomain decoder =
  narrativeDomainsDiffer
    (trans
      (sym (editorialLabelCorrect decoder))
      (trans
        (cong (decodeNarrativeFromLabel decoder) samePublicLabel)
        (inWorldLabelCorrect decoder)))

------------------------------------------------------------------------
-- Applicability is another independent fibre coordinate.
------------------------------------------------------------------------

data InspectionDecision : Set where
  decideAtThisLevel : InspectionDecision
  rechartBeforeDecision : InspectionDecision

inspectionDecision : HigherOrderClassState → InspectionDecision
inspectionDecision state with applicability state
... | Level.applicableHere = decideAtThisLevel
... | Level.noTypedMeetAtCurrentLevel = rechartBeforeDecision
... | Level.outsideCurrentComparisonScope = rechartBeforeDecision
... | Level.projectionCollapsedRequiredCoordinate = rechartBeforeDecision

editorialDecisionHere :
  inspectionDecision editorialSecondOrderState ≡ decideAtThisLevel
editorialDecisionHere = refl

inWorldDecisionRequiresRechart :
  inspectionDecision inWorldSecondOrderState ≡ rechartBeforeDecision
inWorldDecisionRequiresRechart = refl

record OrderOnlyDecisionDecoder : Set where
  constructor orderOnlyDecisionDecoder
  field
    decodeDecisionFromOrder : ClassOrder → InspectionDecision
    editorialDecisionCorrect :
      decodeDecisionFromOrder (classOrder editorialSecondOrderState)
      ≡ decideAtThisLevel
    inWorldDecisionCorrect :
      decodeDecisionFromOrder (classOrder inWorldSecondOrderState)
      ≡ rechartBeforeDecision

open OrderOnlyDecisionDecoder public

inspectionDecisionNotFactorableThroughClassOrder :
  OrderOnlyDecisionDecoder → ⊥
inspectionDecisionNotFactorableThroughClassOrder decoder =
  let
    impossible : decideAtThisLevel ≡ rechartBeforeDecision
    impossible =
      trans
        (sym (editorialDecisionCorrect decoder))
        (trans
          (cong (decodeDecisionFromOrder decoder) sameClassOrder)
          (inWorldDecisionCorrect decoder))
  in
  case impossible of λ where ()

------------------------------------------------------------------------
-- Boundary: order, fiction, and applicability must not collapse.
------------------------------------------------------------------------

record HigherOrderFictionBoundary : Set where
  constructor higherOrderFictionBoundary
  field
    secondOrderMeansFictional : Bool
    fictionalMeansSecondOrder : Bool
    editorialAboutFictionMeansInWorldFictional : Bool
    sameLabelMeansSameNarrativeDomain : Bool
    sameOrderMeansSameApplicability : Bool
    noTypedMeetMeansGloballyFalse : Bool
    preserveOrthogonalCoordinates : Bool

canonicalHigherOrderFictionBoundary : HigherOrderFictionBoundary
canonicalHigherOrderFictionBoundary =
  higherOrderFictionBoundary false false false false false false true
