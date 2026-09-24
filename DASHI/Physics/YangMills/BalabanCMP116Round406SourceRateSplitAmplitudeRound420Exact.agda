{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116Round406SourceRateSplitAmplitudeRound420Exact where

------------------------------------------------------------------------
-- B / ROUND420: SOURCE RATE SPLIT -> R406 DOMAIN AMPLITUDES
--
-- CMP116 Sect. 1, especially (1.23)--(1.29), retains tree-length decay after
-- the fixed-Y differentiated sum and spends only part of that decay on the
-- localization-domain counting in (1.26)--(1.28).
--
-- The active R414 API had represented the outcome by two independent leaves
--
--   commonYShell(Y) <= A_Y W(d_Y)
--   sum_Y A_Y       <= A_src.
--
-- This owner uses the source-native rate split instead:
--
--   commonYShell(Y) <= C * (E(d_Y) * W(d_Y))
--   sum_Y E(d_Y)    <= E_src.
--
-- It defines A_Y = C E(d_Y), A_src = C E_src and proves BOTH R414
-- obligations by finite ordered-real algebra.  Hence outer amplitude control is
-- no longer an independent theorem once the literal source fixed-Y rate split
-- and weighted-fibre estimate have been attached to the exact R406 domains.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.List.Base using (List; []; _∷_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; _+ℝ_ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; +-mono-≤
  ; *-assoc ; *-distribˡ-+ ; mulZeroʳ
  ; mulMonotoneNonnegative )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportGraphRound416Exact as Graph
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116Round406SupportGraphGeometryExact as Geometry
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum

------------------------------------------------------------------------
-- Finite positive-sum algebra.
------------------------------------------------------------------------

sumNonnegative :
  ∀ {A : Set} (f : A → ℝ) (xs : List A) →
  (∀ x → 0ℝ ≤ℝ f x) →
  0ℝ ≤ℝ Resum.sumℝ f xs
sumNonnegative f [] nonnegative = ≤ℝ-refl
sumNonnegative f (x ∷ xs) nonnegative =
  +-mono-≤
    (nonnegative x)
    (sumNonnegative f xs nonnegative)

scaleFiniteSum :
  ∀ {A : Set} (constant : ℝ) (f : A → ℝ) (xs : List A) →
  constant *ℝ Resum.sumℝ f xs
  ≡
  Resum.sumℝ (λ x → constant *ℝ f x) xs
scaleFiniteSum constant f [] =
  mulZeroʳ constant
scaleFiniteSum constant f (x ∷ xs) =
  trans
    (*-distribˡ-+ constant (f x) (Resum.sumℝ f xs))
    (cong
      (λ tail → constant *ℝ f x +ℝ tail)
      (scaleFiniteSum constant f xs))

------------------------------------------------------------------------
-- Literal source rate split on the exact R406 domain family.
------------------------------------------------------------------------

record LiteralRound406SourceRateSplit
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

    -- W is the residual decay deliberately retained for the physical
    -- two-source separation after the entropy payment.
    decay : R414.AntitoneNonnegativeDecayWeight

    -- C is the fixed source prefactor; E is the entropy-paying half-weight.
    sourcePrefactor : ℝ
    sourcePrefactorNonnegative : 0ℝ ≤ℝ sourcePrefactor

    entropyHalfWeight : Nat → ℝ
    entropyHalfWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ entropyHalfWeight depth

    entropyAllowance : ℝ

    -- Fixed-Y source localization after splitting the available tree decay.
    fixedYRateSplit :
      ∀ domain →
      R406.commonYShell application domain
      ≤ℝ
      sourcePrefactor *ℝ
        (entropyHalfWeight
          (Graph.domainTreeDistance supportGraph domain)
        *ℝ
        R414.weight decay
          (Graph.domainTreeDistance supportGraph domain))

    -- Counting/fibre estimate from the same source tree coordinate.
    weightedFibreBudget :
      Resum.sumℝ
        (λ domain →
          entropyHalfWeight
            (Graph.domainTreeDistance supportGraph domain))
        (R406.localizedDomains application)
      ≤ℝ entropyAllowance

open LiteralRound406SourceRateSplit public

domainAmplitude :
  ∀ {Measure TestObservable dataSet extension base application} →
  LiteralRound406SourceRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  R406.Domain application → ℝ
domainAmplitude source domain =
  sourcePrefactor source *ℝ
    entropyHalfWeight source
      (Graph.domainTreeDistance (supportGraph source) domain)

sourceAmplitude :
  ∀ {Measure TestObservable dataSet extension base application} →
  LiteralRound406SourceRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  ℝ
sourceAmplitude source =
  sourcePrefactor source *ℝ entropyAllowance source

domainAmplitudeNonnegative :
  ∀ {Measure TestObservable dataSet extension base application}
    (source : LiteralRound406SourceRateSplit
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} {base = base}
      application) →
  ∀ domain →
  0ℝ ≤ℝ domainAmplitude source domain
domainAmplitudeNonnegative source domain =
  subst
    (λ lower → lower ≤ℝ domainAmplitude source domain)
    (mulZeroʳ 0ℝ)
    (mulMonotoneNonnegative
      ≤ℝ-refl
      (sourcePrefactorNonnegative source)
      ≤ℝ-refl
      (entropyHalfWeightNonnegative source
        (Graph.domainTreeDistance (supportGraph source) domain)))

commonYShellBelowCompiledDomainDecay :
  ∀ {Measure TestObservable dataSet extension base application}
    (source : LiteralRound406SourceRateSplit
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} {base = base}
      application) →
  ∀ domain →
  R406.commonYShell application domain
  ≤ℝ
  domainAmplitude source domain
    *ℝ R414.weight (decay source)
      (Graph.domainTreeDistance (supportGraph source) domain)
commonYShellBelowCompiledDomainDecay {application = application} source domain =
  subst
    (λ upper → R406.commonYShell application domain ≤ℝ upper)
    (sym
      (*-assoc
        (sourcePrefactor source)
        (entropyHalfWeight source
          (Graph.domainTreeDistance (supportGraph source) domain))
        (R414.weight (decay source)
          (Graph.domainTreeDistance (supportGraph source) domain))))
    (fixedYRateSplit source domain)

compiledAmplitudeSumBelowSourceAmplitude :
  ∀ {Measure TestObservable dataSet extension base application}
    (source : LiteralRound406SourceRateSplit
      {Measure = Measure} {TestObservable = TestObservable}
      {dataSet = dataSet} {extension = extension} {base = base}
      application) →
  Resum.sumℝ
    (domainAmplitude source)
    (R406.localizedDomains application)
  ≤ℝ
  sourceAmplitude source
compiledAmplitudeSumBelowSourceAmplitude
    {application = application} source =
  let
    halfWeight =
      λ domain →
        entropyHalfWeight source
          (Graph.domainTreeDistance (supportGraph source) domain)

    halfWeightSumNonnegative :
      0ℝ ≤ℝ
      Resum.sumℝ halfWeight (R406.localizedDomains application)
    halfWeightSumNonnegative =
      sumNonnegative
        halfWeight
        (R406.localizedDomains application)
        (λ domain →
          entropyHalfWeightNonnegative source
            (Graph.domainTreeDistance (supportGraph source) domain))

    scaledBudget :
      sourcePrefactor source *ℝ
        Resum.sumℝ halfWeight (R406.localizedDomains application)
      ≤ℝ
      sourcePrefactor source *ℝ entropyAllowance source
    scaledBudget =
      mulMonotoneNonnegative
        (sourcePrefactorNonnegative source)
        ≤ℝ-refl
        halfWeightSumNonnegative
        (weightedFibreBudget source)

    factored :
      sourcePrefactor source *ℝ
        Resum.sumℝ halfWeight (R406.localizedDomains application)
      ≡
      Resum.sumℝ
        (domainAmplitude source)
        (R406.localizedDomains application)
    factored =
      scaleFiniteSum
        (sourcePrefactor source)
        halfWeight
        (R406.localizedDomains application)
  in
  subst
    (λ left → left ≤ℝ sourceAmplitude source)
    factored
    scaledBudget

asSupportGraphGeometry :
  ∀ {Measure TestObservable dataSet extension base}
    (application : R406.SelectedCMP116TermwiseLocalization base) →
  LiteralRound406SourceRateSplit
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    application →
  Geometry.Round406SupportGraphGeometry application
asSupportGraphGeometry application source = record
  { Geometry.Round406SupportGraphGeometry.supportGraph =
      supportGraph source
  ; Geometry.Round406SupportGraphGeometry.representativeTerm =
      representativeTerm source
  ; Geometry.Round406SupportGraphGeometry.representativeSurvives =
      representativeSurvives source
  ; Geometry.Round406SupportGraphGeometry.decay =
      decay source
  ; Geometry.Round406SupportGraphGeometry.domainAmplitude =
      domainAmplitude source
  ; Geometry.Round406SupportGraphGeometry.domainAmplitudeNonnegative =
      domainAmplitudeNonnegative source
  ; Geometry.Round406SupportGraphGeometry.commonYShellBelowDomainDecay =
      commonYShellBelowCompiledDomainDecay source
  ; Geometry.Round406SupportGraphGeometry.sourceAmplitude =
      sourceAmplitude source
  ; Geometry.Round406SupportGraphGeometry.amplitudeSumBelowSourceAmplitude =
      compiledAmplitudeSumBelowSourceAmplitude source
  }

round420RateSplitFiniteSumCompilerLevel : ProofLevel
round420RateSplitFiniteSumCompilerLevel = machineChecked

-- No caller now supplies an arbitrary A_Y family plus an unrelated outer
-- summability proof: both are constructed above from the source rate split.
round420SeparateOuterAmplitudeLeafRequired : ProofLevel
round420SeparateOuterAmplitudeLeafRequired = machineChecked

-- The remaining theorem is the SAME-object/source attachment: instantiate
-- fixedYRateSplit and weightedFibreBudget on the exact R406 localization
-- domains and the exact support-tree metric.  CMP116 (1.23)--(1.29) is the
-- primary source authority for that statement.
literalR406FixedYRateSplitAndWeightedFibreAttachmentLevel : ProofLevel
literalR406FixedYRateSplitAndWeightedFibreAttachmentLevel = conditional
