{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116CanonicalLiteralRateSourceRound438Exact where

------------------------------------------------------------------------
-- B / ROUND438: PUT CMP116 (1.26)--(1.29) DIRECTLY ON THE R429 CARRIER
--
-- R422 previously required three same-object equalities:
--   source domains = R406 domains
--   source tree distance = support-tree distance
--   source fixed-Y shell = R406 commonYShell.
--
-- On the preferred Goal-1 route these are unnecessary.  Define the published
-- source theorem record directly with those literal coordinates.  All three
-- attachment equalities become refl; the only remaining source mathematics is
-- the actual fixed-Y rate estimate and weighted-fibre/counting estimate.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.Closure.YMEffectiveActionSupportInterface as Support
import DASHI.Physics.YangMills.YMSupportGraphDistance as Graph
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116DifferentiatedLocalizationSourceExact as Source
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116CanonicalSelectedBSourceRound435Exact as R435
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred

record CanonicalLiteralCMP116RateSource
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

    sourcePrefactor : ℝ
    sourcePrefactorNonnegative : 0ℝ ≤ℝ sourcePrefactor

    entropyHalfWeight residualDecayWeight : Nat → ℝ
    entropyHalfWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ entropyHalfWeight depth
    residualDecayWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ residualDecayWeight depth
    residualDecayWeightAntitone :
      ∀ {smaller larger} →
      Nat._≤_ smaller larger →
      residualDecayWeight larger ≤ℝ residualDecayWeight smaller

    entropyAllowance : ℝ

    -- This is the genuine local analytic source theorem on the literal shell.
    literalFixedYEquation129RateSplit :
      ∀ domain →
      R429.commonYShell fourStage domain
      ≤ℝ
      sourcePrefactor *ℝ
        (entropyHalfWeight Graph.ymTreeEdgeCount
         *ℝ residualDecayWeight Graph.ymTreeEdgeCount)

    -- This is the genuine CMP116 (1.26)--(1.28) counting/tree estimate on the
    -- exact retained domain family.  Lean's connected-domain counting theorem
    -- can be used as a donor for this field after carrier identification.
    literalEquation126128WeightedFibreBudget :
      Resum.sumℝ
        (λ _ → entropyHalfWeight Graph.ymTreeEdgeCount)
        (R429.localizedDomains fourStage)
      ≤ℝ entropyAllowance

open CanonicalLiteralCMP116RateSource public

publishedRateSource :
  ∀ {Measure TestObservable dataSet extension base}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base} →
  CanonicalLiteralCMP116RateSource fourStage →
  Source.PublishedCMP116Equation126129RateSplit
    (R429.Domain fourStage)
publishedRateSource {fourStage = fourStage} data = record
  { Source.PublishedCMP116Equation126129RateSplit.localizedDomains =
      R429.localizedDomains fourStage
  ; Source.PublishedCMP116Equation126129RateSplit.sourceTreeDistance =
      λ _ → Graph.ymTreeEdgeCount
  ; Source.PublishedCMP116Equation126129RateSplit.sourcePrefactor =
      sourcePrefactor data
  ; Source.PublishedCMP116Equation126129RateSplit.sourcePrefactorNonnegative =
      sourcePrefactorNonnegative data
  ; Source.PublishedCMP116Equation126129RateSplit.entropyHalfWeight =
      entropyHalfWeight data
  ; Source.PublishedCMP116Equation126129RateSplit.residualDecayWeight =
      residualDecayWeight data
  ; Source.PublishedCMP116Equation126129RateSplit.entropyHalfWeightNonnegative =
      entropyHalfWeightNonnegative data
  ; Source.PublishedCMP116Equation126129RateSplit.residualDecayWeightNonnegative =
      residualDecayWeightNonnegative data
  ; Source.PublishedCMP116Equation126129RateSplit.residualDecayWeightAntitone =
      residualDecayWeightAntitone data
  ; Source.PublishedCMP116Equation126129RateSplit.entropyAllowance =
      entropyAllowance data
  ; Source.PublishedCMP116Equation126129RateSplit.fixedYShell =
      R429.commonYShell fourStage
  ; Source.PublishedCMP116Equation126129RateSplit.fixedYEquation129RateSplit =
      literalFixedYEquation129RateSplit data
  ; Source.PublishedCMP116Equation126129RateSplit.equation126128WeightedFibreBudget =
      literalEquation126128WeightedFibreBudget data
  }

asCanonicalSelectedBSource :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  CanonicalLiteralCMP116RateSource fourStage →
  R435.CanonicalSelectedBSource fourStage
asCanonicalSelectedBSource fourStage data = record
  { R435.CanonicalSelectedBSource.leftMark = leftMark data
  ; R435.CanonicalSelectedBSource.rightMark = rightMark data
  ; R435.CanonicalSelectedBSource.CarriesLink = CarriesLink data
  ; R435.CanonicalSelectedBSource.everySelectedTermCarriesLeft =
      everySelectedTermCarriesLeft data
  ; R435.CanonicalSelectedBSource.everySelectedTermCarriesRight =
      everySelectedTermCarriesRight data
  ; R435.CanonicalSelectedBSource.selectedHead = selectedHead data
  ; R435.CanonicalSelectedBSource.selectedTail = selectedTail data
  ; R435.CanonicalSelectedBSource.retainedFibreIsHeadTail =
      retainedFibreIsHeadTail data
  ; R435.CanonicalSelectedBSource.source = publishedRateSource data
  ; R435.CanonicalSelectedBSource.sourceDomainsAreLiteralDomains = refl
  ; R435.CanonicalSelectedBSource.sourceTreeDistanceIsCanonicalSupportTree =
      λ _ → refl
  ; R435.CanonicalSelectedBSource.sourceFixedYShellIsLiteralCommonYShell =
      λ _ → refl
  }

preferredR415 :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  CanonicalLiteralCMP116RateSource fourStage →
  Preferred.PreferredR415Source
    (R429.Domain fourStage)
    (R429.Term fourStage)
    (R429.Operator fourStage)
preferredR415 fourStage data =
  R435.preferredR415 fourStage
    (asCanonicalSelectedBSource fourStage data)

round438SourceCoordinateAttachmentLevel : ProofLevel
round438SourceCoordinateAttachmentLevel = machineChecked

round438PreferredR415CompilerLevel : ProofLevel
round438PreferredR415CompilerLevel = machineChecked

-- B3 same-object attachment is now gone.  The live B1--B3 source payments are
-- exactly:
-- * canonical scalar/path replay data in R429;
-- * both selected source marks on each retained term;
-- * nonempty retained fibres;
-- * the literal fixed-Y rate estimate above;
-- * the literal weighted-fibre/counting estimate above.
literalRound438CanonicalCMP116RateTheoremLevel : ProofLevel
literalRound438CanonicalCMP116RateTheoremLevel = conditional
