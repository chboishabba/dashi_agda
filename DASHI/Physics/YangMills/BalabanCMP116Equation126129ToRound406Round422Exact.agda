{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Equation126129ToRound406Round422Exact where

------------------------------------------------------------------------
-- B / ROUND422: CMP116 (1.26)--(1.29) -> LITERAL R406 RATE SPLIT
--
-- The source theorem is now proof-bearing in
-- BalabanCMP116DifferentiatedLocalizationSourceExact:
--
--   * (1.26)--(1.28): weighted localization-domain/tree-fibre summability;
--   * (1.29): fixed-Y differentiated sum with residual tree decay.
--
-- This owner pays only the SAME-OBJECT attachment to the literal R406 carrier:
--
--   source localized-domain family = R406.localizedDomains
--   source d_k(Y)                  = R416 support-tree distance
--   source fixed-Y shell           = R406.commonYShell
--
-- Once those coordinates agree, R420's former B3+B4 input is constructed.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as Graph
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as R406R415
import DASHI.Physics.YangMills.BalabanCMP116Round406SourceRateSplitAmplitudeRound420Exact as R420
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

record Equation126129SelectedR406Attachment
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

    representativeTerm :
      R406.Domain application → R406.Term application

    representativeSurvives :
      ∀ domain →
      Graph.selectedDifferentiatedTermSurvives supportGraph
        domain (representativeTerm domain)

    source :
      Source.PublishedCMP116Equation126129RateSplit
        (R406.Domain application)

    sourceDomainsAreR406Domains :
      Source.localizedDomains source
      ≡
      R406.localizedDomains application

    sourceTreeDistanceIsR406SupportTreeDistance :
      ∀ domain →
      Source.sourceTreeDistance source domain
      ≡
      Graph.domainTreeDistance supportGraph domain

    sourceFixedYShellIsR406CommonYShell :
      ∀ domain →
      Source.fixedYShell source domain
      ≡
      R406.commonYShell application domain

open Equation126129SelectedR406Attachment public

sourceDecay :
  ∀ {Measure TestObservable dataSet extension base application} →
  Equation126129SelectedR406Attachment
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R414.AntitoneNonnegativeDecayWeight
sourceDecay attachment = record
  { R414.AntitoneNonnegativeDecayWeight.weight =
      Source.residualDecayWeight (source attachment)
  ; R414.AntitoneNonnegativeDecayWeight.weightNonnegative =
      Source.residualDecayWeightNonnegative (source attachment)
  ; R414.AntitoneNonnegativeDecayWeight.weightAntitone =
      Source.residualDecayWeightAntitone (source attachment)
  }

fixedYRateSplitOnR406 :
  ∀ {Measure TestObservable dataSet extension base application}
    (attachment :
      Equation126129SelectedR406Attachment
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application) →
  ∀ domain →
  R406.commonYShell application domain
  ≤ℝ
  Source.sourcePrefactor (source attachment) *ℝ
    (Source.entropyHalfWeight (source attachment)
      (Graph.domainTreeDistance (supportGraph attachment) domain)
    *ℝ
    R414.weight (sourceDecay attachment)
      (Graph.domainTreeDistance (supportGraph attachment) domain))
fixedYRateSplitOnR406 {application = application} attachment domain =
  let
    src = source attachment
    sourceDistance = Source.sourceTreeDistance src domain
    targetDistance =
      Graph.domainTreeDistance (supportGraph attachment) domain

    sourceBound :
      Source.fixedYShell src domain
      ≤ℝ
      Source.sourcePrefactor src *ℝ
        (Source.entropyHalfWeight src sourceDistance
        *ℝ Source.residualDecayWeight src sourceDistance)
    sourceBound =
      Source.fixedYEquation129RateSplit src domain

    leftTransport :
      R406.commonYShell application domain
      ≤ℝ
      Source.sourcePrefactor src *ℝ
        (Source.entropyHalfWeight src sourceDistance
        *ℝ Source.residualDecayWeight src sourceDistance)
    leftTransport =
      subst
        (λ left →
          left ≤ℝ
          Source.sourcePrefactor src *ℝ
            (Source.entropyHalfWeight src sourceDistance
            *ℝ Source.residualDecayWeight src sourceDistance))
        (sourceFixedYShellIsR406CommonYShell attachment domain)
        sourceBound

    rightEquality :
      Source.sourcePrefactor src *ℝ
        (Source.entropyHalfWeight src sourceDistance
        *ℝ Source.residualDecayWeight src sourceDistance)
      ≡
      Source.sourcePrefactor src *ℝ
        (Source.entropyHalfWeight src targetDistance
        *ℝ Source.residualDecayWeight src targetDistance)
    rightEquality =
      cong
        (λ distance →
          Source.sourcePrefactor src *ℝ
            (Source.entropyHalfWeight src distance
            *ℝ Source.residualDecayWeight src distance))
        (sourceTreeDistanceIsR406SupportTreeDistance attachment domain)
  in
  subst
    (λ right → R406.commonYShell application domain ≤ℝ right)
    rightEquality
    leftTransport

weightedFibreBudgetOnR406 :
  ∀ {Measure TestObservable dataSet extension base application}
    (attachment :
      Equation126129SelectedR406Attachment
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        application) →
  Resum.sumℝ
    (λ domain →
      Source.entropyHalfWeight (source attachment)
        (Graph.domainTreeDistance (supportGraph attachment) domain))
    (R406.localizedDomains application)
  ≤ℝ
  Source.entropyAllowance (source attachment)
weightedFibreBudgetOnR406 {application = application} attachment =
  let
    src = source attachment

    sourceWeight =
      λ domain →
        Source.entropyHalfWeight src
          (Source.sourceTreeDistance src domain)

    targetWeight =
      λ domain →
        Source.entropyHalfWeight src
          (Graph.domainTreeDistance (supportGraph attachment) domain)

    budgetOnR406Domains :
      Resum.sumℝ sourceWeight (R406.localizedDomains application)
      ≤ℝ Source.entropyAllowance src
    budgetOnR406Domains =
      subst
        (λ domains →
          Resum.sumℝ sourceWeight domains
          ≤ℝ Source.entropyAllowance src)
        (sourceDomainsAreR406Domains attachment)
        (Source.equation126128WeightedFibreBudget src)

    weightSumEquality :
      Resum.sumℝ sourceWeight (R406.localizedDomains application)
      ≡
      Resum.sumℝ targetWeight (R406.localizedDomains application)
    weightSumEquality =
      R406R415.sumCongruent
        (R406.localizedDomains application)
        sourceWeight
        targetWeight
        (λ domain →
          cong
            (Source.entropyHalfWeight src)
            (sourceTreeDistanceIsR406SupportTreeDistance
              attachment domain))
  in
  subst
    (λ left → left ≤ℝ Source.entropyAllowance src)
    weightSumEquality
    budgetOnR406Domains

compileLiteralRound406SourceRateSplit :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
  Equation126129SelectedR406Attachment
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R420.LiteralRound406SourceRateSplit application
compileLiteralRound406SourceRateSplit application attachment = record
  { R420.LiteralRound406SourceRateSplit.supportGraph =
      supportGraph attachment
  ; R420.LiteralRound406SourceRateSplit.representativeTerm =
      representativeTerm attachment
  ; R420.LiteralRound406SourceRateSplit.representativeSurvives =
      representativeSurvives attachment
  ; R420.LiteralRound406SourceRateSplit.decay =
      sourceDecay attachment
  ; R420.LiteralRound406SourceRateSplit.sourcePrefactor =
      Source.sourcePrefactor (source attachment)
  ; R420.LiteralRound406SourceRateSplit.sourcePrefactorNonnegative =
      Source.sourcePrefactorNonnegative (source attachment)
  ; R420.LiteralRound406SourceRateSplit.entropyHalfWeight =
      Source.entropyHalfWeight (source attachment)
  ; R420.LiteralRound406SourceRateSplit.entropyHalfWeightNonnegative =
      Source.entropyHalfWeightNonnegative (source attachment)
  ; R420.LiteralRound406SourceRateSplit.entropyAllowance =
      Source.entropyAllowance (source attachment)
  ; R420.LiteralRound406SourceRateSplit.fixedYRateSplit =
      fixedYRateSplitOnR406 attachment
  ; R420.LiteralRound406SourceRateSplit.weightedFibreBudget =
      weightedFibreBudgetOnR406 attachment
  }

round422SourceTheoremTransportCompilerLevel : ProofLevel
round422SourceTheoremTransportCompilerLevel = machineChecked

-- The source analysis itself is now owned by the standard-imported
-- PublishedCMP116Equation126129RateSplit.  The remaining selected-carrier debt
-- is exactly the three same-object identifications stored in the attachment.
literalEquation126129SelectedR406SameObjectAttachmentLevel : ProofLevel
literalEquation126129SelectedR406SameObjectAttachmentLevel = conditional
