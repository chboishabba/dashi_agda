{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116R406ToSelectedMarkedExpansionRound417Exact where

------------------------------------------------------------------------
-- ROUND417 / R406 LITERAL SOURCE EXPANSION -> R415 CANONICAL MARKED EXPANSION
--
-- R406 already owns the literal CMP116 expansion structure:
--
--   localized domains,
--   common-Y term lists,
--   common-Y and outer-boundary sum equalities,
--   fixed-Y term-majorant summability,
--   selected CMP119/T5 source coordinates.
--
-- R415 should not ask for those a second time.  The only refinement required
-- here is to show that each existing R406 term is the canonical R410
-- CMP99/CMP109 marked-path term and that the existing R406 majorant is exactly
-- R410's canonical marked-product majorant.  The newer R411/R414 support
-- connection and outer amplitude/tree data are then attached once.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; 0ℝ; _*ℝ_; absℝ; _≤ℝ_)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanNoncommutativeMarkedOperatorProductExact as Marked
import DASHI.Physics.YangMills.BalabanCMP109FourStageOperatorFactorRound407Exact as R407
import DASHI.Physics.YangMills.BalabanCMP99MarkedStageDifferenceRound408Exact as R408
import DASHI.Physics.YangMills.BalabanCMP99SingleMarkedFourStageRound409Exact as R409

record R406CanonicalR410Refinement
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base) : Set₂ where
  field
    replay :
      R406.Domain application →
      R406.Term application →
      R410.CanonicalPathMarkedCMP109Replay (R406.Operator application) ℝ

    -- Exact scalarization of the SAME R406 differentiated term.
    differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm :
      ∀ domain term →
      absℝ (R406.differentiatedTerm application domain term)
      ≡
      Marked.operatorNorm
        (R408.telescopeAlgebra
          (R410.stageDifference (replay domain term)))
        (Marked.difference
          (R408.telescopeAlgebra
            (R410.stageDifference (replay domain term)))
          (Marked.operatorProduct
            (R408.telescopeAlgebra
              (R410.stageDifference (replay domain term)))
            (R407.stageOperator
              (R407.before
                (R408.ordinaryPair
                  (R410.stageDifference (replay domain term))))
              R407.cmp109DerivativeStages)
          (Marked.operatorProduct
            (R408.telescopeAlgebra
              (R410.stageDifference (replay domain term)))
            (R407.stageOperator
              (R407.after
                (R408.ordinaryPair
                  (R410.stageDifference (replay domain term))))
              R407.cmp109DerivativeStages))

    -- Representation equality only: the R406 majorant is not a second
    -- fixed-Y estimate; it is the canonical R410 marked-product majorant.
    r406MajorantIsCanonicalR410Majorant :
      ∀ domain term →
      R406.differentiatedTermMajorant application domain term
      ≡
      Marked.markedProductMajorant
        (R408.telescopeAlgebra
          (R410.stageDifference (replay domain term)))
        (R407.ordinaryStageMajorant
          (R408.ordinaryPair
            (R410.stageDifference (replay domain term))))
        (R409.stageMarkedMajorant
          (R410.stageDifference (replay domain term))
          (R410.canonicalSingleChangedAgreement (replay domain term)))
        R407.cmp109DerivativeStages

open R406CanonicalR410Refinement public

selectedR410Term :
  ∀ {Measure TestObservable dataSet extension base}
    {application : R406.SelectedCMP116TermwiseLocalization base} →
  R406CanonicalR410Refinement application →
  R406.Domain application →
  R406.Term application →
  R410.SelectedCMP116PathMarkedTerm (R406.Operator application)
selectedR410Term refinement domain term = record
  { R410.SelectedCMP116PathMarkedTerm.replay =
      replay refinement domain term
  ; R410.SelectedCMP116PathMarkedTerm.differentiatedTerm =
      R406.differentiatedTerm _ domain term
  ; R410.SelectedCMP116PathMarkedTerm.differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm =
      differentiatedTermAbsoluteIsCanonicalProductDifferenceNorm
        refinement domain term
  }

canonicalTermMajorantIsR406Majorant :
  ∀ {Measure TestObservable dataSet extension base}
    {application : R406.SelectedCMP116TermwiseLocalization base}
    (refinement : R406CanonicalR410Refinement application)
    domain term →
  R415.canonicalTermMajorant
    (selectedR410Term refinement domain term)
  ≡
  R406.differentiatedTermMajorant application domain term
canonicalTermMajorantIsR406Majorant refinement domain term =
  sym (r406MajorantIsCanonicalR410Majorant refinement domain term)

-- Tiny finite-sum congruence needed only to transport the already-owned R406
-- fixed-Y summability theorem onto the definitionally refined R410 majorants.
sumPointwiseEquality :
  ∀ {A : Set}
    (xs : List A)
    (left right : A → ℝ) →
  (∀ x → left x ≡ right x) →
  Resum.sumℝ left xs ≡ Resum.sumℝ right xs
sumPointwiseEquality [] left right pointwise = refl
sumPointwiseEquality (x ∷ xs) left right pointwise
  rewrite pointwise x
        | sumPointwiseEquality xs left right pointwise = refl

sumCanonicalMajorantsBelowCommonYShell :
  ∀ {Measure TestObservable dataSet extension base}
    {application : R406.SelectedCMP116TermwiseLocalization base}
    (refinement : R406CanonicalR410Refinement application)
    domain →
  Resum.sumℝ
    (λ term →
      R415.canonicalTermMajorant
        (selectedR410Term refinement domain term))
    (R406.termsWithCommonY application domain)
  ≤ℝ
  R406.commonYShell application domain
sumCanonicalMajorantsBelowCommonYShell
    {application = application} refinement domain =
  let
    r406Bound =
      R406.differentiatedMajorantsBelowCommonYShell application domain
  in
  subst
    (λ lower → lower ≤ℝ R406.commonYShell application domain)
    (sumPointwiseEquality
      (R406.termsWithCommonY application domain)
      (λ term →
        R415.canonicalTermMajorant
          (selectedR410Term refinement domain term))
      (R406.differentiatedTermMajorant application domain)
      (canonicalTermMajorantIsR406Majorant refinement domain))
    r406Bound

record R406ToR415GeometryAndCounting
    {Measure TestObservable : Set}
    {dataSet : Gram.PhysicalMeasureConvergenceData Measure TestObservable ℚ}
    {extension : R278.ScalarCovarianceConvergenceExtension dataSet}
    {base : R318.UnlocalizedT5StateFamilyJPresentation dataSet extension}
    (application : R406.SelectedCMP116TermwiseLocalization base) : Set₂ where
  field
    geometry :
      R411.SelectedSupportConnectionGeometry
        (R406.Domain application) (R406.Term application)

    decay : R414.AntitoneNonnegativeDecayWeight

    everyLocalizedDomainConnects :
      ∀ domain → R411.domainConnectsBothSupports geometry domain

    domainAmplitude : R406.Domain application → ℝ
    domainAmplitudeNonnegative :
      ∀ domain → 0ℝ ≤ℝ domainAmplitude domain

    commonYShellBelowDomainDecay :
      ∀ domain →
      R406.commonYShell application domain
      ≤ℝ
      domainAmplitude domain *ℝ R414.weight decay (R411.domainTreeDistance geometry domain)

    sourceAmplitude : ℝ

    amplitudeSumBelowSourceAmplitude :
      Resum.sumℝ domainAmplitude (R406.localizedDomains application)
      ≤ℝ sourceAmplitude

open R406ToR415GeometryAndCounting public

asSelectedCMP116MarkedExpansion :
  ∀ {Measure TestObservable dataSet extension base}
    {application : R406.SelectedCMP116TermwiseLocalization base} →
  (refinement : R406CanonicalR410Refinement application) →
  R406ToR415GeometryAndCounting application →
  R415.SelectedCMP116MarkedExpansion
    (R406.Domain application) (R406.Term application) (R406.Operator application)
asSelectedCMP116MarkedExpansion
    {application = application} refinement counting = record
  { R415.SelectedCMP116MarkedExpansion.localizedDomains =
      R406.localizedDomains application
  ; R415.SelectedCMP116MarkedExpansion.termsWithCommonY =
      R406.termsWithCommonY application
  ; R415.SelectedCMP116MarkedExpansion.selectedTerm =
      selectedR410Term refinement
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIntegrand =
      R406.commonYBoundaryIntegrand application
  ; R415.SelectedCMP116MarkedExpansion.commonYShell =
      R406.commonYShell application
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIntegrand =
      R406.selectedBoundaryIntegrand application
  ; R415.SelectedCMP116MarkedExpansion.commonYBoundaryIsSelectedTermSum =
      R406.commonYBoundaryIsTermSum application
  ; R415.SelectedCMP116MarkedExpansion.selectedBoundaryIsCommonYSum =
      R406.selectedBoundaryIsCommonYSum application
  ; R415.SelectedCMP116MarkedExpansion.selectedR410MajorantsBelowCommonYShell =
      sumCanonicalMajorantsBelowCommonYShell refinement
  ; R415.SelectedCMP116MarkedExpansion.geometry =
      geometry counting
  ; R415.SelectedCMP116MarkedExpansion.decay =
      decay counting
  ; R415.SelectedCMP116MarkedExpansion.everyLocalizedDomainConnects =
      everyLocalizedDomainConnects counting
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitude =
      domainAmplitude counting
  ; R415.SelectedCMP116MarkedExpansion.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative counting
  ; R415.SelectedCMP116MarkedExpansion.commonYShellBelowDomainDecay =
      commonYShellBelowDomainDecay counting
  ; R415.SelectedCMP116MarkedExpansion.sourceAmplitude =
      sourceAmplitude counting
  ; R415.SelectedCMP116MarkedExpansion.amplitudeSumBelowSourceAmplitude =
      amplitudeSumBelowSourceAmplitude counting
  }

round417R406ExpansionReuseCompilerLevel : ProofLevel
round417R406ExpansionReuseCompilerLevel = machineChecked

round417DuplicateLiteralExpansionFieldsRequired : Bool
round417DuplicateLiteralExpansionFieldsRequired = false
