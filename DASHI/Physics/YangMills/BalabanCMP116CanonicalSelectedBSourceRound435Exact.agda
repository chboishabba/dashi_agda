{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact where

-- GOAL-1 NOTE (Round440):
-- This module is retained as a compatibility/coarse-support route.  Its R416
-- support metric identifies every domain with the global YM tree-edge count.
-- The preferred Goal-1 CMP116 (1.26)--(1.29) path is Round440, which carries
-- the literal variable per-domain d_k(Y) : Domain -> Nat.

------------------------------------------------------------------------
-- B / ROUND435: CANONICAL FOUR-STAGE + TWICE-MARKED SUPPORT + CMP116 SOURCE
--
-- Highest-alpha literal B constructor.
--
-- R429 already builds the R406 term carrier definitionally on the canonical
-- CMP99/CMP109 four-stage derivative replay.  Rather than changing that term
-- carrier again, this owner equips the SAME term values with the two literal
-- selected source-link witnesses and retained-fibre nonemptiness.
--
-- Consequently:
--   * R406/R410 layout is compiler-owned (R429);
--   * survival is common-Y list membership;
--   * survivor -> both selected marks is compiler-owned here;
--   * graph/tree metrics are canonical YMSupportGraphDistance coordinates;
--   * R423 representative choice is compiler-owned;
--   * R422 source (1.26)--(1.29) transport is compiler-owned;
--   * R425 then constructs PreferredR415Source.
--
-- The remaining source mathematics is exactly:
--   (i) actual canonical differentiated terms carry both selected source marks;
--  (ii) every retained common-Y fibre is nonempty;
-- (iii) source CMP116 domains/tree/shell are these literal R429 coordinates.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as R416
import DASHI.Physics.YangMills.BalabanCMP116Round406NonemptySelectedFibreRound423Exact as R423
import DASHI.Physics.YangMills.BalabanCMP116LiteralBCompletionRound425Exact as R425
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred

record CanonicalSelectedBSource
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    : Set₁ where
  field
    leftMark rightMark : Support.Link

    CarriesLink : R429.Term fourStage → Support.Link → Set

    everySelectedTermCarriesLeft :
      ∀ domain term →
      term ∈ R429.termsWithCommonY fourStage domain →
      CarriesLink term leftMark

    everySelectedTermCarriesRight :
      ∀ domain term →
      term ∈ R429.termsWithCommonY fourStage domain →
      CarriesLink term rightMark

    selectedHead : R429.Domain fourStage → R429.Term fourStage
    selectedTail : R429.Domain fourStage → List (R429.Term fourStage)

    retainedFibreIsHeadTail :
      ∀ domain →
      R429.termsWithCommonY fourStage domain
      ≡ selectedHead domain ∷ selectedTail domain

    source :
      Source.PublishedCMP116Equation126129RateSplit
        (R429.Domain fourStage)

    sourceDomainsAreLiteralDomains :
      Source.localizedDomains source
      ≡ R429.localizedDomains fourStage

    sourceTreeDistanceIsCanonicalSupportTree :
      ∀ domain →
      Source.sourceTreeDistance source domain
      ≡ Graph.ymTreeEdgeCount

    sourceFixedYShellIsLiteralCommonYShell :
      ∀ domain →
      Source.fixedYShell source domain
      ≡ R429.commonYShell fourStage domain

open CanonicalSelectedBSource public

containsSelectedLink :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (selected :
      CanonicalSelectedBSource
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  R429.Domain fourStage → Support.Link → Set
containsSelectedLink {fourStage = fourStage} selected domain link =
  Σ (R429.Term fourStage)
    (λ term →
      term ∈ R429.termsWithCommonY fourStage domain
      × CarriesLink selected term link)

supportGraph :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (selected :
      CanonicalSelectedBSource
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  R416.SelectedTwoMarkSupportGraph
    (R429.Domain fourStage)
    (R429.Term fourStage)
supportGraph {fourStage = fourStage} selected = record
  { R416.SelectedTwoMarkSupportGraph.leftMark = leftMark selected
  ; R416.SelectedTwoMarkSupportGraph.rightMark = rightMark selected
  ; R416.SelectedTwoMarkSupportGraph.selectedConnectingDistance =
      Graph.ymGraphDist (leftMark selected) (rightMark selected)
  ; R416.SelectedTwoMarkSupportGraph.selectedDistanceIsSupportGraphDistance =
      refl
  ; R416.SelectedTwoMarkSupportGraph.domainTreeDistance =
      λ _ → Graph.ymTreeEdgeCount
  ; R416.SelectedTwoMarkSupportGraph.domainTreeDistanceIsSupportTreeEdgeCount =
      λ _ → refl
  ; R416.SelectedTwoMarkSupportGraph.containsSelectedLink =
      containsSelectedLink selected
  ; R416.SelectedTwoMarkSupportGraph.selectedDifferentiatedTermSurvives =
      λ domain term →
        term ∈ R429.termsWithCommonY fourStage domain
  ; R416.SelectedTwoMarkSupportGraph.survivingTermContainsLeftMark =
      λ domain term membership →
        term , (membership ,
          everySelectedTermCarriesLeft selected domain term membership)
  ; R416.SelectedTwoMarkSupportGraph.survivingTermContainsRightMark =
      λ domain term membership →
        term , (membership ,
          everySelectedTermCarriesRight selected domain term membership)
  }

nonemptyFibre :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (selected :
      CanonicalSelectedBSource
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  R423.NonemptySelectedCommonYFibre
    (R429.canonicalApplication fourStage)
nonemptyFibre {fourStage = fourStage} selected = record
  { R423.NonemptySelectedCommonYFibre.selectedHead =
      selectedHead selected
  ; R423.NonemptySelectedCommonYFibre.selectedTail =
      selectedTail selected
  ; R423.NonemptySelectedCommonYFibre.termsWithCommonYIsHeadTail =
      retainedFibreIsHeadTail selected
  }

membershipSupport :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (selected :
      CanonicalSelectedBSource
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  R423.SelectedCommonYMembershipSupport
    (R429.canonicalApplication fourStage)
membershipSupport selected = record
  { R423.SelectedCommonYMembershipSupport.supportGraph =
      supportGraph selected
  ; R423.SelectedCommonYMembershipSupport.selectedListMembershipImpliesSurvival =
      λ domain term membership → membership
  }

asR423Attachment :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  CanonicalSelectedBSource fourStage →
  R423.Equation126129SelectedR406NonemptyAttachment
    (R429.canonicalApplication fourStage)
asR423Attachment fourStage selected = record
  { R423.Equation126129SelectedR406NonemptyAttachment.nonemptyFibre =
      nonemptyFibre selected
  ; R423.Equation126129SelectedR406NonemptyAttachment.membershipSupport =
      membershipSupport selected
  ; R423.Equation126129SelectedR406NonemptyAttachment.source =
      source selected
  ; R423.Equation126129SelectedR406NonemptyAttachment.sourceDomainsAreR406Domains =
      sourceDomainsAreLiteralDomains selected
  ; R423.Equation126129SelectedR406NonemptyAttachment.sourceTreeDistanceIsR406SupportTreeDistance =
      sourceTreeDistanceIsCanonicalSupportTree selected
  ; R423.Equation126129SelectedR406NonemptyAttachment.sourceFixedYShellIsR406CommonYShell =
      sourceFixedYShellIsLiteralCommonYShell selected
  }

literalBCompletion :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  CanonicalSelectedBSource fourStage →
  R425.LiteralCMP116BCompletion
    (R429.canonicalApplication fourStage)
literalBCompletion fourStage selected =
  R425.fromCanonicalFourStage fourStage
    (asR423Attachment fourStage selected)

preferredR415 :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  CanonicalSelectedBSource fourStage →
  Preferred.PreferredR415Source
    (R429.Domain fourStage)
    (R429.Term fourStage)
    (R429.Operator fourStage)
preferredR415 fourStage selected =
  R425.preferredR415 (literalBCompletion fourStage selected)

round435CanonicalSupportCompilerLevel : ProofLevel
round435CanonicalSupportCompilerLevel = machineChecked

round435CanonicalBCompletionCompilerLevel : ProofLevel
round435CanonicalBCompletionCompilerLevel = machineChecked

-- Goal-1 B1/B2/B3 have now been stripped to the actual source mathematics:
-- canonical differentiated terms carry both selected J-links, retained fibres
-- are nonempty, and CMP116's source domain/tree/shell coordinates are exactly
-- the canonical R429 ones.  No factor-layout/support/representative/metric
-- theorem remains downstream.
literalRound435CanonicalSelectedSourceLevel : ProofLevel
literalRound435CanonicalSelectedSourceLevel = conditional
