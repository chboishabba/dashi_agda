{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406NonemptySelectedFibreRound423Exact where

------------------------------------------------------------------------
-- B / ROUND423: NONEMPTY COMMON-Y FIBRES -> REPRESENTATIVE SURVIVING TERM
--
-- R419/R422 only need one surviving twice-marked term per retained domain in
-- order to invoke R416 support-graph geometry.  The choice of that term is not
-- mathematical content.  The real content is:
--
--   * every retained R406 common-Y term list is nonempty;
--   * membership in that selected list implies the support-graph
--     "surviving differentiated term" predicate.
--
-- This module compiles those facts into the representativeTerm /
-- representativeSurvives pair expected by R422.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as Graph
import DASHI.Physics.YangMills.BalabanCMP116Equation126129ToRound406Round422Exact as R422

record NonemptySelectedCommonYFibre
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    selectedHead : R406.Domain application → R406.Term application
    selectedTail :
      R406.Domain application → List (R406.Term application)

    termsWithCommonYIsHeadTail :
      ∀ domain →
      R406.termsWithCommonY application domain
      ≡ selectedHead domain ∷ selectedTail domain

open NonemptySelectedCommonYFibre public

selectedHeadBelongs :
  ∀ {Measure TestObservable dataSet extension base application}
    (fibre :
      NonemptySelectedCommonYFibre
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application) →
  ∀ domain →
  selectedHead fibre domain
  ∈ R406.termsWithCommonY application domain
selectedHeadBelongs {application = application} fibre domain =
  subst
    (λ terms → selectedHead fibre domain ∈ terms)
    (sym (termsWithCommonYIsHeadTail fibre domain))
    (here refl)

record SelectedCommonYMembershipSupport
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    supportGraph :
      Graph.SelectedTwoMarkSupportGraph
        (R406.Domain application)
        (R406.Term application)

    selectedListMembershipImpliesSurvival :
      ∀ domain term →
      term ∈ R406.termsWithCommonY application domain →
      Graph.selectedDifferentiatedTermSurvives supportGraph domain term

open SelectedCommonYMembershipSupport public

representativeSurvivesFromMembership :
  ∀ {Measure TestObservable dataSet extension base application}
    (fibre :
      NonemptySelectedCommonYFibre
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application)
    (membership :
      SelectedCommonYMembershipSupport
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application) →
  ∀ domain →
  Graph.selectedDifferentiatedTermSurvives
    (supportGraph membership)
    domain
    (selectedHead fibre domain)
representativeSurvivesFromMembership fibre membership domain =
  selectedListMembershipImpliesSurvival membership
    domain
    (selectedHead fibre domain)
    (selectedHeadBelongs fibre domain)

record Equation126129SelectedR406NonemptyAttachment
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    nonemptyFibre :
      NonemptySelectedCommonYFibre application

    membershipSupport :
      SelectedCommonYMembershipSupport application

    source :
      Source.PublishedCMP116Equation126129RateSplit
        (R406.Domain application)

    sourceDomainsAreR406Domains :
      Source.localizedDomains source
      ≡ R406.localizedDomains application

    sourceTreeDistanceIsR406SupportTreeDistance :
      ∀ domain →
      Source.sourceTreeDistance source domain
      ≡
      Graph.domainTreeDistance
        (supportGraph membershipSupport)
        domain

    sourceFixedYShellIsR406CommonYShell :
      ∀ domain →
      Source.fixedYShell source domain
      ≡ R406.commonYShell application domain

open Equation126129SelectedR406NonemptyAttachment public

asRound422Attachment :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
  Equation126129SelectedR406NonemptyAttachment
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R422.Equation126129SelectedR406Attachment application
asRound422Attachment application attachment = record
  { R422.Equation126129SelectedR406Attachment.supportGraph =
      supportGraph (membershipSupport attachment)
  ; R422.Equation126129SelectedR406Attachment.representativeTerm =
      selectedHead (nonemptyFibre attachment)
  ; R422.Equation126129SelectedR406Attachment.representativeSurvives =
      representativeSurvivesFromMembership
        (nonemptyFibre attachment)
        (membershipSupport attachment)
  ; R422.Equation126129SelectedR406Attachment.source =
      source attachment
  ; R422.Equation126129SelectedR406Attachment.sourceDomainsAreR406Domains =
      sourceDomainsAreR406Domains attachment
  ; R422.Equation126129SelectedR406Attachment.sourceTreeDistanceIsR406SupportTreeDistance =
      sourceTreeDistanceIsR406SupportTreeDistance attachment
  ; R422.Equation126129SelectedR406Attachment.sourceFixedYShellIsR406CommonYShell =
      sourceFixedYShellIsR406CommonYShell attachment
  }

round423RepresentativeChoiceCompilerLevel : ProofLevel
round423RepresentativeChoiceCompilerLevel = machineChecked

-- The representative choice is gone.  The remaining B2 source content is
-- exactly nonemptiness of each retained selected common-Y fibre, membership ->
-- selected-survival, and the two-mark/metric fields inside the support graph.
literalRound406SelectedFibreNonemptyAndMembershipLevel : ProofLevel
literalRound406SelectedFibreNonemptyAndMembershipLevel = conditional
