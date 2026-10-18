{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanCMP116VariableDomainPreferredR415Round440Exact where

------------------------------------------------------------------------
-- B / ROUND440: VARIABLE-DOMAIN CMP116 d_k(Y) -> PREFERRED R415 DIRECTLY
--
-- R416/R434 used a single global YM tree-edge count as the tree coordinate.
-- That is sufficient for a coarse support-distance upper bound, but it is not
-- the literal CMP116 d_k(Y) appearing in (1.26)--(1.29).
--
-- This preferred Goal-1 owner bypasses that coarse wrapper.  Each retained
-- localization domain carries its own tree distance
--
--     domainTreeDistance : Domain -> Nat
--
-- and the source theorem proves directly
--
--     d_selected <= d_Y.
--
-- The R429 term list already has the exact canonical R410 majorant sum below
-- commonYShell, so the R415 fixed-Y charging field is compiler-owned here.
-- The remaining analytic inputs are exactly the variable-Y source rate split
-- and its weighted-fibre/counting budget.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
import Data.Nat.Base as Nat
open import Data.List.Base using (List; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Rational.Base as ℚ using (ℚ)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  ( ℝ ; 0ℝ ; absℝ ; _*ℝ_ ; _≤ℝ_
  ; ≤ℝ-refl ; *-assoc ; mulZeroʳ ; mulMonotoneNonnegative )
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.BalabanConnectedCovarianceExpectationLimitRound278Exact as R278
import DASHI.Physics.YangMills.BalabanT5UnlocalizedJSourceLocalizationRound318Exact as R318
import DASHI.Physics.YangMills.BalabanMarkedPolarisationResummation as Resum
import DASHI.Physics.YangMills.BalabanCMP116CanonicalFourStageR406Round429Exact as R429
import DASHI.Physics.YangMills.BalabanCMP116SelectedTermwiseLocalizationRound406Exact as R406
import DASHI.Physics.YangMills.BalabanCMP116Round406ExactR410ReplayRound421Exact as R421
import DASHI.Physics.YangMills.BalabanCMP116Round406To415Exact as Replay
import DASHI.Physics.YangMills.BalabanCMP116CanonicalPathMarkedReplayRound410Exact as R410
import DASHI.Physics.YangMills.BalabanCMP116SelectedMarkedExpansionRound415Exact as R415
import DASHI.Physics.YangMills.BalabanCMP116SelectedSupportConnectionRound411Exact as R411
import DASHI.Physics.YangMills.BalabanCMP116ConnectingOuterSumRound414Exact as R414
import DASHI.Physics.YangMills.BalabanCMP116Round354To415FixedYExact as FixedY
import DASHI.Physics.YangMills.BalabanCMP116Round406SourceRateSplitAmplitudeRound420Exact as R420
import DASHI.Physics.YangMills.BalabanCMP116PreferredR415SourceExact as Preferred

record VariableDomainCMP116Source
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
    -- Literal support semantics on the SAME R429 term values.
    CarriesLeft CarriesRight : R429.Term fourStage → Set

    everySelectedTermCarriesLeft :
      ∀ domain term →
      term ∈ R429.termsWithCommonY fourStage domain →
      CarriesLeft term

    everySelectedTermCarriesRight :
      ∀ domain term →
      term ∈ R429.termsWithCommonY fourStage domain →
      CarriesRight term

    -- Retained domains are exactly those with a nonempty selected fibre.
    selectedHead : R429.Domain fourStage → R429.Term fourStage
    selectedTail : R429.Domain fourStage → List (R429.Term fourStage)
    retainedFibreIsHeadTail :
      ∀ domain →
      R429.termsWithCommonY fourStage domain
      ≡ selectedHead domain ∷ selectedTail domain

    -- Literal source geometry.  Unlike R416 this coordinate varies with Y.
    selectedConnectingDistance : Nat
    domainTreeDistance : R429.Domain fourStage → Nat

    selectedDistanceBelowDomainTree :
      ∀ domain →
      selectedConnectingDistance Nat.≤ domainTreeDistance domain

    -- Residual physical decay deliberately retained after the entropy payment.
    residualDecayWeight : Nat → ℝ
    residualDecayWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ residualDecayWeight depth
    residualDecayWeightAntitone :
      ∀ {near far} →
      near Nat.≤ far →
      residualDecayWeight far ≤ℝ residualDecayWeight near

    sourcePrefactor : ℝ
    sourcePrefactorNonnegative : 0ℝ ≤ℝ sourcePrefactor

    entropyHalfWeight : Nat → ℝ
    entropyHalfWeightNonnegative :
      ∀ depth → 0ℝ ≤ℝ entropyHalfWeight depth

    entropyAllowance : ℝ

    -- CMP116 (1.29) on the literal variable-Y tree coordinate.
    literalFixedYEquation129RateSplit :
      ∀ domain →
      R429.commonYShell fourStage domain
      ≤ℝ
      sourcePrefactor *ℝ
        (entropyHalfWeight (domainTreeDistance domain)
         *ℝ residualDecayWeight (domainTreeDistance domain))

    -- CMP116 (1.26)--(1.28) on the exact retained R429 domain family.
    literalEquation126128WeightedFibreBudget :
      Resum.sumℝ
        (λ domain → entropyHalfWeight (domainTreeDistance domain))
        (R429.localizedDomains fourStage)
      ≤ℝ entropyAllowance

open VariableDomainCMP116Source public

application :
  ∀ {Measure TestObservable dataSet extension base}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base} →
  VariableDomainCMP116Source fourStage →
  R406.SelectedCMP116TermwiseLocalization base
application {fourStage = fourStage} source =
  R429.canonicalApplication fourStage

exactReplay :
  ∀ {Measure TestObservable dataSet extension base}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    (source : VariableDomainCMP116Source fourStage) →
  Replay.Round406ExactR410Replay (R429.canonicalApplication fourStage)
exactReplay {fourStage = fourStage} source =
  R421.compileExactR410Replay
    (R429.canonicalApplication fourStage)
    (R429.canonicalOperatorReplay fourStage)

selectedTerm :
  ∀ {Measure TestObservable dataSet extension base}
    {fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base}
    (source : VariableDomainCMP116Source fourStage) →
  R429.Domain fourStage →
  R429.Term fourStage →
  R410.SelectedCMP116PathMarkedTerm (R429.Operator fourStage)
selectedTerm source =
  Replay.selectedR410Term (exactReplay source)

selectedHeadBelongs :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage)
    domain →
  selectedHead source domain
  ∈ R429.termsWithCommonY fourStage domain
selectedHeadBelongs {fourStage = fourStage} source domain =
  subst
    (λ terms → selectedHead source domain ∈ terms)
    (sym (retainedFibreIsHeadTail source domain))
    (here refl)

DomainConnectsBothSupports :
  ∀ {Measure TestObservable dataSet extension base fourStage} →
  VariableDomainCMP116Source
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    fourStage →
  R429.Domain fourStage → Set
DomainConnectsBothSupports {fourStage = fourStage} source domain =
  Σ (R429.Term fourStage)
    (λ term →
      term ∈ R429.termsWithCommonY fourStage domain
      × CarriesLeft source term
      × CarriesRight source term)

everyLocalizedDomainConnects :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage)
    domain →
  DomainConnectsBothSupports source domain
everyLocalizedDomainConnects source domain =
  selectedHead source domain ,
    ( selectedHeadBelongs source domain
    , everySelectedTermCarriesLeft source domain
        (selectedHead source domain)
        (selectedHeadBelongs source domain)
    , everySelectedTermCarriesRight source domain
        (selectedHead source domain)
        (selectedHeadBelongs source domain)
    )

geometry :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  R411.SelectedSupportConnectionGeometry
    (R429.Domain fourStage)
    (R429.Term fourStage)
geometry {fourStage = fourStage} source = record
  { R411.SelectedSupportConnectionGeometry.selectedConnectingDistance =
      selectedConnectingDistance source
  ; R411.SelectedSupportConnectionGeometry.domainTreeDistance =
      domainTreeDistance source
  ; R411.SelectedSupportConnectionGeometry.selectedDifferentiatedTermSurvives =
      λ domain term →
        term ∈ R429.termsWithCommonY fourStage domain
  ; R411.SelectedSupportConnectionGeometry.domainConnectsBothSupports =
      DomainConnectsBothSupports source
  ; R411.SelectedSupportConnectionGeometry.survivingTermForcesSupportConnection =
      λ domain term membership →
        term ,
          ( membership
          , everySelectedTermCarriesLeft source domain term membership
          , everySelectedTermCarriesRight source domain term membership
          )
  ; R411.SelectedSupportConnectionGeometry.supportConnectionForcesDistanceLower =
      λ domain _ → selectedDistanceBelowDomainTree source domain
  }

decay :
  ∀ {Measure TestObservable dataSet extension base fourStage} →
  VariableDomainCMP116Source
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    fourStage →
  R414.AntitoneNonnegativeDecayWeight
decay source = record
  { R414.AntitoneNonnegativeDecayWeight.weight =
      residualDecayWeight source
  ; R414.AntitoneNonnegativeDecayWeight.weightNonnegative =
      residualDecayWeightNonnegative source
  ; R414.AntitoneNonnegativeDecayWeight.weightAntitone =
      residualDecayWeightAntitone source
  }

fixedYCharging :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  FixedY.R415FixedYCharging
    (R429.termsWithCommonY fourStage)
    (selectedTerm source)
    (R429.commonYShell fourStage)
fixedYCharging {fourStage = fourStage} source = record
  { FixedY.R415FixedYCharging.chargedMajorant =
      λ domain term →
        R406.differentiatedTermMajorant
          (R429.canonicalApplication fourStage) domain term
  ; FixedY.R415FixedYCharging.canonicalR410BelowCharged =
      λ domain term →
        subst
          (λ right →
            R415.canonicalTermMajorant (selectedTerm source domain term)
            ≤ℝ right)
          (sym
            (Replay.differentiatedMajorantIsCanonicalR410
              (exactReplay source) domain term))
          ≤ℝ-refl
  ; FixedY.R415FixedYCharging.chargedCMP116Summability =
      R406.differentiatedMajorantsBelowCommonYShell
        (R429.canonicalApplication fourStage)
  }

domainAmplitude :
  ∀ {Measure TestObservable dataSet extension base fourStage} →
  VariableDomainCMP116Source
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    fourStage →
  R429.Domain fourStage → ℝ
domainAmplitude source domain =
  sourcePrefactor source *ℝ
    entropyHalfWeight source (domainTreeDistance source domain)

sourceAmplitude :
  ∀ {Measure TestObservable dataSet extension base fourStage} →
  VariableDomainCMP116Source
    {Measure = Measure} {TestObservable = TestObservable}
    {dataSet = dataSet} {extension = extension} {base = base}
    fourStage →
  ℝ
sourceAmplitude source =
  sourcePrefactor source *ℝ entropyAllowance source

domainAmplitudeNonnegative :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage)
    domain →
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
        (domainTreeDistance source domain)))

commonYShellBelowDomainDecay :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage)
    domain →
  R429.commonYShell fourStage domain
  ≤ℝ
  domainAmplitude source domain
    *ℝ R414.weight (decay source) (domainTreeDistance source domain)
commonYShellBelowDomainDecay {fourStage = fourStage} source domain =
  subst
    (λ upper →
      R429.commonYShell fourStage domain ≤ℝ upper)
    (sym
      (*-assoc
        (sourcePrefactor source)
        (entropyHalfWeight source (domainTreeDistance source domain))
        (residualDecayWeight source (domainTreeDistance source domain))))
    (literalFixedYEquation129RateSplit source domain)

amplitudeSumBelowSourceAmplitude :
  ∀ {Measure TestObservable dataSet extension base fourStage}
    (source :
      VariableDomainCMP116Source
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} {base = base}
        fourStage) →
  Resum.sumℝ
    (domainAmplitude source)
    (R429.localizedDomains fourStage)
  ≤ℝ sourceAmplitude source
amplitudeSumBelowSourceAmplitude {fourStage = fourStage} source =
  let
    halfWeight =
      λ domain →
        entropyHalfWeight source (domainTreeDistance source domain)

    halfWeightSumNonnegative :
      0ℝ ≤ℝ
      Resum.sumℝ halfWeight (R429.localizedDomains fourStage)
    halfWeightSumNonnegative =
      R420.sumNonnegative
        halfWeight
        (R429.localizedDomains fourStage)
        (λ domain →
          entropyHalfWeightNonnegative source
            (domainTreeDistance source domain))

    scaledBudget :
      sourcePrefactor source *ℝ
        Resum.sumℝ halfWeight (R429.localizedDomains fourStage)
      ≤ℝ
      sourcePrefactor source *ℝ entropyAllowance source
    scaledBudget =
      mulMonotoneNonnegative
        (sourcePrefactorNonnegative source)
        ≤ℝ-refl
        halfWeightSumNonnegative
        (literalEquation126128WeightedFibreBudget source)

    factored :
      sourcePrefactor source *ℝ
        Resum.sumℝ halfWeight (R429.localizedDomains fourStage)
      ≡
      Resum.sumℝ
        (domainAmplitude source)
        (R429.localizedDomains fourStage)
    factored =
      R420.scaleFiniteSum
        (sourcePrefactor source)
        halfWeight
        (R429.localizedDomains fourStage)
  in
  subst
    (λ left → left ≤ℝ sourceAmplitude source)
    factored
    scaledBudget

preferredR415 :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base) →
  VariableDomainCMP116Source fourStage →
  Preferred.PreferredR415Source
    (R429.Domain fourStage)
    (R429.Term fourStage)
    (R429.Operator fourStage)
preferredR415 fourStage source = record
  { Preferred.PreferredR415Source.localizedDomains =
      R429.localizedDomains fourStage
  ; Preferred.PreferredR415Source.termsWithCommonY =
      R429.termsWithCommonY fourStage
  ; Preferred.PreferredR415Source.selectedTerm =
      selectedTerm source
  ; Preferred.PreferredR415Source.commonYBoundaryIntegrand =
      R429.commonYBoundaryIntegrand fourStage
  ; Preferred.PreferredR415Source.commonYShell =
      R429.commonYShell fourStage
  ; Preferred.PreferredR415Source.selectedBoundaryIntegrand =
      R429.selectedBoundaryIntegrand fourStage
  ; Preferred.PreferredR415Source.commonYBoundaryIsSelectedTermSum =
      λ domain →
        trans
          (R406.commonYBoundaryIsTermSum
            (R429.canonicalApplication fourStage) domain)
          (Replay.sumCongruent
            (R429.termsWithCommonY fourStage domain)
            (R406.differentiatedTerm
              (R429.canonicalApplication fourStage) domain)
            (λ term → R410.differentiatedTerm (selectedTerm source domain term))
            (Replay.differentiatedTermIsR410
              (exactReplay source) domain))
  ; Preferred.PreferredR415Source.selectedBoundaryIsCommonYSum =
      R429.selectedBoundaryIsCommonYSum fourStage
  ; Preferred.PreferredR415Source.fixedYCharging =
      fixedYCharging source
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

selectedBoundaryBelowVariableDomainDecay :
  ∀ {Measure TestObservable dataSet extension base}
    (fourStage :
      R429.CanonicalFourStageR406Data
        {Measure = Measure} {TestObservable = TestObservable}
        {dataSet = dataSet} {extension = extension} base)
    (source : VariableDomainCMP116Source fourStage) →
  absℝ
    (R429.selectedBoundaryIntegrand fourStage)
  ≤ℝ
  sourceAmplitude source
    *ℝ residualDecayWeight source (selectedConnectingDistance source)
selectedBoundaryBelowVariableDomainDecay fourStage source =
  Preferred.preferredR415SelectedBoundaryDecay
    (preferredR415 fourStage source)

round440R429ToR410CompilerLevel : ProofLevel
round440R429ToR410CompilerLevel = machineChecked

round440FixedYChargingCompilerLevel : ProofLevel
round440FixedYChargingCompilerLevel = machineChecked

round440VariableDomainOuterSumCompilerLevel : ProofLevel
round440VariableDomainOuterSumCompilerLevel = machineChecked

round440PreferredR415CompilerLevel : ProofLevel
round440PreferredR415CompilerLevel = machineChecked

-- Live B source mathematics after removing the global-tree-coordinate bug:
--   B1 actual CMP116 scalar/path data inhabit R429;
--   B2 retained fibres are nonempty and selected terms carry both source marks;
--   B3 source geometry supplies the true per-domain d_k(Y) and d_sel <= d_k(Y);
--   B4 CMP116 (1.29) fixed-Y rate split on that d_k(Y);
--   B5 CMP116 (1.26)--(1.28) weighted domain/tree counting on that d_k(Y).
-- R410 replay, fixed-Y majorant summation, outer amplitude factorization and
-- extraction of the common selected-distance decay are compiler-owned.
literalRound440VariableDomainCMP116SourceLevel : ProofLevel
literalRound440VariableDomainCMP116SourceLevel = conditional
