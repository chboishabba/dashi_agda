module DASHI.Ontology.WikidataHigherOrderFictionContextExact where

------------------------------------------------------------------------
-- HIGHER-ORDER CLASS / FICTION / CONTEXT FACTORISATION
--
-- Wikidata's class-order documentation defines a second-order class by the
-- order of its instances: its instances are first-order classes.  That is an
-- order-of-predication coordinate.  It does not by itself answer whether the
-- class is editorially about fiction, exists only inside a fictional world,
-- has member-classes whose instances are fictional individuals, is an ordinary
-- real-world modelling class, or is even applicable at the current inspection
-- level.
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
  memberClassesClassifyFictionalIndividuals : NarrativeDomain
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
-- Three distinct readings can occupy the same public label/order.
------------------------------------------------------------------------

-- Reading 1: a real editorial/metamodel class whose members are classes used
-- to organise fiction.
editorialSecondOrderState : HigherOrderClassState
editorialSecondOrderState =
  higherOrderClassState
    "fictional second-order class"
    secondOrder
    editoriallyAboutFiction
    Level.applicableHere
    "editorial/metamodel classification about fictional first-order classes"

-- Reading 2: a second-order class interpreted as existing within a fictional
-- world.  This is deliberately a countermodel carrier, not a claim that the
-- live Wikidata item has this semantics.
inWorldSecondOrderState : HigherOrderClassState
inWorldSecondOrderState =
  higherOrderClassState
    "fictional second-order class"
    secondOrder
    inWorldFictionalDomain
    Level.outsideCurrentComparisonScope
    "countermodel: second-order classification interpreted inside a fictional world"

-- Reading 3: an ordinary modelling class of classes, where the member classes
-- themselves classify fictional individuals.  This differs from saying that
-- the metaclass itself is an in-world fictional entity.
memberClassSecondOrderState : HigherOrderClassState
memberClassSecondOrderState =
  higherOrderClassState
    "fictional second-order class"
    secondOrder
    memberClassesClassifyFictionalIndividuals
    Level.applicableHere
    "class of classes whose instances are fictional individuals"

samePublicLabelEditorialInWorld :
  publicLabel editorialSecondOrderState ≡ publicLabel inWorldSecondOrderState
samePublicLabelEditorialInWorld = refl

samePublicLabelEditorialMemberClass :
  publicLabel editorialSecondOrderState ≡ publicLabel memberClassSecondOrderState
samePublicLabelEditorialMemberClass = refl

sameClassOrderEditorialInWorld :
  classOrder editorialSecondOrderState ≡ classOrder inWorldSecondOrderState
sameClassOrderEditorialInWorld = refl

sameClassOrderEditorialMemberClass :
  classOrder editorialSecondOrderState ≡ classOrder memberClassSecondOrderState
sameClassOrderEditorialMemberClass = refl

editorialDiffersFromInWorld :
  editoriallyAboutFiction ≡ inWorldFictionalDomain → ⊥
editorialDiffersFromInWorld ()

editorialDiffersFromMemberClassSemantics :
  editoriallyAboutFiction ≡ memberClassesClassifyFictionalIndividuals → ⊥
editorialDiffersFromMemberClassSemantics ()

inWorldDiffersFromMemberClassSemantics :
  inWorldFictionalDomain ≡ memberClassesClassifyFictionalIndividuals → ⊥
inWorldDiffersFromMemberClassSemantics ()

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
  editorialDiffersFromInWorld
    (trans
      (sym (editorialCorrect decoder))
      (trans
        (cong (decodeNarrativeFromOrder decoder) sameClassOrderEditorialInWorld)
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
  editorialDiffersFromInWorld
    (trans
      (sym (editorialLabelCorrect decoder))
      (trans
        (cong (decodeNarrativeFromLabel decoder) samePublicLabelEditorialInWorld)
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

memberClassDecisionHere :
  inspectionDecision memberClassSecondOrderState ≡ decideAtThisLevel
memberClassDecisionHere = refl

inspectionDecisionsDiffer :
  decideAtThisLevel ≡ rechartBeforeDecision → ⊥
inspectionDecisionsDiffer ()

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
  inspectionDecisionsDiffer
    (trans
      (sym (editorialDecisionCorrect decoder))
      (trans
        (cong (decodeDecisionFromOrder decoder) sameClassOrderEditorialInWorld)
        (inWorldDecisionCorrect decoder)))

------------------------------------------------------------------------
-- Live Wikidata calibration surface, kept distinct from theorem semantics.
------------------------------------------------------------------------

record WikidataFictionCalibration : Set where
  constructor wikidataFictionCalibration
  field
    fictionalProfessionQid : String
    fictionalProfessionHasFictionalMetaclass : Bool
    fictionalProfessionHasFictionalSecondOrderClass : Bool
    fictionalSecondOrderClassQid : String
    calibrationDate : String

canonicalWikidataFictionCalibration : WikidataFictionCalibration
canonicalWikidataFictionCalibration =
  wikidataFictionCalibration
    "Q17305127"
    true
    true
    "Q126371087"
    "2026-08-19"

------------------------------------------------------------------------
-- Boundary: order, fiction, member-domain, and applicability must not collapse.
------------------------------------------------------------------------

record HigherOrderFictionBoundary : Set where
  constructor higherOrderFictionBoundary
  field
    secondOrderMeansFictional : Bool
    fictionalMeansSecondOrder : Bool
    editorialAboutFictionMeansInWorldFictional : Bool
    editorialAboutFictionMeansMemberClassesFictional : Bool
    memberClassesFictionalMeansMetaclassInWorldFictional : Bool
    sameLabelMeansSameNarrativeDomain : Bool
    sameOrderMeansSameApplicability : Bool
    noTypedMeetMeansGloballyFalse : Bool
    preserveOrthogonalCoordinates : Bool

canonicalHigherOrderFictionBoundary : HigherOrderFictionBoundary
canonicalHigherOrderFictionBoundary =
  higherOrderFictionBoundary false false false false false false false false true
