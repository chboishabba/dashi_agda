{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116LiteralSelectedExpansionRound418Exact where

------------------------------------------------------------------------
-- ROUND418 / ONE SOURCE-NATIVE INHABITANT FOR THE PREFERRED B EXPANSION
--
-- Combine:
--   R406  literal boundary/common-Y decomposition,
--   R410  exact selected differentiated term,
--   R416  marked charging + published fixed-Y summability,
--   R411  two-support geometry,
--   R414  positive outer localization sum.
--
-- Important simplification: R406's independently named differentiated
-- majorant is no longer used.  The exact R410 canonical majorant is charged
-- directly by R416, so no extra majorant-equality weld is required.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import Data.Rational.Base as ℚ using (ℚ)

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116LiteralMarkedChargingRound416Exact as R416
import DASHI.Physics.YangMills.BalabanCMP116LiteralMarkedChargingToR415Exact as R417
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

record LiteralSelectedCMP116Expansion
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base)
    : Set₁ where
  field
    selectedR410Term :
      R406.Domain application →
      R406.Term application →
      R410.SelectedCMP116PathMarkedTerm (R406.Operator application)

    differentiatedTermIsR410 :
      ∀ domain term →
      R406.differentiatedTerm application domain term
      ≡ R410.differentiatedTerm (selectedR410Term domain term)

    fixedYCharging :
      R417.LiteralR415FixedYCharging
        (R406.Domain application)
        (R406.Term application)
        (R406.Operator application)
        (R406.termsWithCommonY application)
        selectedR410Term
        (R406.commonYShell application)

    geometry :
      R411.SelectedSupportConnectionGeometry
        (R406.Domain application) (R406.Term application)

    decay : R414.AntitoneNonnegativeDecayWeight

    everyLocalizedDomainConnects :
      ∀ domain →
      R411.domainConnectsBothSupports geometry domain

    domainAmplitude : R406.Domain application → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      R406.commonYShell application domain
      ≤ℝ domainAmplitude domain
        *ℝ R414.weight decay (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude (R406.localizedDomains application)
      ≤ℝ sourceAmplitude

open LiteralSelectedCMP116Expansion public

sumR410TermsIsR406TermSum :
  ∀ {Measure TestObservable dataSet extension base application}
    (source : LiteralSelectedCMP116Expansion
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} {base = base}
      application)
    domain →
  Resum.sumℝ
    (λ term → R406.differentiatedTerm application domain term)
    (R406.termsWithCommonY application domain)
  ≡
  Resum.sumℝ
    (λ term → R410.differentiatedTerm
      (selectedR410Term source domain term))
    (R406.termsWithCommonY application domain)
sumR410TermsIsR406TermSum {application = application} source domain =
  sumCongruent
    (R406.termsWithCommonY application domain)
    (R406.differentiatedTerm application domain)
    (λ term → R410.differentiatedTerm
      (selectedR410Term source domain term))
    (differentiatedTermIsR410 source domain)
  where
  sumCongruent :
    ∀ {A : Set} (xs : Data.List.Base.List A)
      (left right : A → ℝ) →
    (∀ x → left x ≡ right x) →
    Resum.sumℝ left xs ≡ Resum.sumℝ right xs
  sumCongruent Data.List.Base.[] left right pointwise =
    Agda.Builtin.Equality.refl
  sumCongruent (Data.List.Base._∷_ x xs) left right pointwise
    rewrite pointwise x
          | sumCongruent xs left right pointwise =
    Agda.Builtin.Equality.refl

asPreferredR415Source :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
  LiteralSelectedCMP116Expansion
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  Preferred.PreferredR415Source
    (R406.Domain application)
    (R406.Term application)
    (R406.Operator application)
asPreferredR415Source application source = record
  { Preferred.PreferredR415Source.localizedDomains =
      R406.localizedDomains application
  ; Preferred.PreferredR415Source.termsWithCommonY =
      R406.termsWithCommonY application
  ; Preferred.PreferredR415Source.selectedTerm =
      selectedR410Term source
  ; Preferred.PreferredR415Source.commonYBoundaryIntegrand =
      R406.commonYBoundaryIntegrand application
  ; Preferred.PreferredR415Source.commonYShell =
      R406.commonYShell application
  ; Preferred.PreferredR415Source.selectedBoundaryIntegrand =
      R406.selectedBoundaryIntegrand application
  ; Preferred.PreferredR415Source.commonYBoundaryIsSelectedTermSum =
      λ domain →
        Relation.Binary.PropositionalEquality.trans
          (R406.commonYBoundaryIsTermSum application domain)
          (sumR410TermsIsR406TermSum source domain)
  ; Preferred.PreferredR415Source.selectedBoundaryIsCommonYSum =
      R406.selectedBoundaryIsCommonYSum application
  ; Preferred.PreferredR415Source.fixedYCharging =
      R417.asFixedYCharging (fixedYCharging source)
  ; Preferred.PreferredR415Source.geometry =
      geometry source
  ; Preferred.PreferredR415Source.decay =
      decay source
  ; Preferred.PreferredR415Source.everyLocalizedDomainConnects =
      everyLocalizedDomainConnects source
  ; Preferred.PreferredR415Source.domainAmplitude =
      domainAmplitude source
  ; Preferred.PreferredR415Source.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative source
  ; Preferred.PreferredR415Source.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay source
  ; Preferred.PreferredR415Source.sourceAmplitude =
      sourceAmplitude source
  ; Preferred.PreferredR415Source.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude source
  }

literalSelectedCMP116ExpansionCompilerLevel : ProofLevel
literalSelectedCMP116ExpansionCompilerLevel = machineChecked

-- Remaining B source object after R418:
--   exact R406 term -> R410 scalarization,
--   Round416 same-object charge/summability attachments,
--   R411 two-support geometry,
--   R414 per-domain amplitude/tree-decay summability.
literalSelectedCMP116ExpansionSourceLevel : ProofLevel
literalSelectedCMP116ExpansionSourceLevel = conditional
