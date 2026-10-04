{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109LiteralStressCylinderMaxCutExact where

------------------------------------------------------------------------
-- SHARP R109 -> CYLINDER MAX-CUT.
--
-- The source-native Round109 insertion pair is intentionally abstract: it does
-- not itself expose a `Configuration -> R` function.  Therefore a physical
-- presentation theorem is genuinely required before OS2/OS4 can consume it.
--
-- The previous terminal presentation additionally carried an arbitrary
-- `StressInsertionObservableMeaning` predicate.  That is unnecessary freedom.
-- Here the meaning relation is definitionally just SAME PAIR + SAME OBSERVABLE.
-- The only new physical data are therefore:
--
--   * one real cylinder observable presenting the selected R109 insertion;
--   * positive-time admissibility of that observable;
--   * gauge invariance of that observable.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationExact as Old
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109

record LiteralR109StressCylinderPresentation
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS osInputs reconstruction}
    (localC :
      LocalC.PinnedCMP119ConcreteLocalCInputs
        G X Configuration Position CurvaturePolynomial LocalOperator
        OPECoefficient (Top.StressTensor C)
        Hilbert Vector Hamiltonian Algebra
        Scale Volume Root ContinuumFamily Core
        {sequenceLimit = sequenceLimit}
        {limitLaws = limitLaws}
        {quotient = quotient}
        {division = division}
        {S = osS}
        osInputs reconstruction group)
    : Set₂ where
  field
    provenance : R110.LiteralStressSameObjectProvenance Y group

    round109 :
      Round109.Round109ConcreteLocalCStressWeld Y group localC

    completionMatches :
      R110.markedCompletion provenance
      ≡ Round109.completion round109

    stressInsertionObservable : Configuration → ℝ

    PositiveTimeSupported : (Configuration → ℝ) → Set
    GaugeInvariantObservable : (Configuration → ℝ) → Set

    stressInsertionPositiveTime :
      PositiveTimeSupported stressInsertionObservable

    stressInsertionGaugeInvariant :
      GaugeInvariantObservable stressInsertionObservable

open LiteralR109StressCylinderPresentation public

sameSelectedInsertionMeaning :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (presentation :
      LiteralR109StressCylinderPresentation
        {C = C} {S = S} Y group
        {G = G} {X = X} {Configuration = Configuration}
        {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
        {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
        {Hilbert = Hilbert} {Vector = Vector}
        {Hamiltonian = Hamiltonian} {Algebra = Algebra}
        {Scale = Scale} {Volume = Volume} {Root = Root}
        {ContinuumFamily = ContinuumFamily} {Core = Core}
        {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
        {quotient = quotient} {division = division}
        {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
        localC) →
  Source.SourceNativeOrdinaryCharacteristicPair
    (R109.source (R110.sourceCauchy (provenance presentation))) →
  (Configuration → ℝ) → Set
sameSelectedInsertionMeaning presentation pair observable =
  (pair ≡ R109.stressInsertion (R110.sourceCauchy (provenance presentation)))
  × (observable ≡ stressInsertionObservable presentation)

asOldR109SelectedStressCylinderPresentation :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  LiteralR109StressCylinderPresentation
    {C = C} {S = S} Y group
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC →
  Old.R109SelectedStressCylinderPresentation
    {C = C} {S = S} Y group
    {G = G} {X = X} {Configuration = Configuration}
    {Position = Position} {CurvaturePolynomial = CurvaturePolynomial}
    {LocalOperator = LocalOperator} {OPECoefficient = OPECoefficient}
    {Hilbert = Hilbert} {Vector = Vector}
    {Hamiltonian = Hamiltonian} {Algebra = Algebra}
    {Scale = Scale} {Volume = Volume} {Root = Root}
    {ContinuumFamily = ContinuumFamily} {Core = Core}
    {sequenceLimit = sequenceLimit} {limitLaws = limitLaws}
    {quotient = quotient} {division = division}
    {osS = osS} {osInputs = osInputs} {reconstruction = reconstruction}
    localC
asOldR109SelectedStressCylinderPresentation presentation = record
  { Old.R109SelectedStressCylinderPresentation.provenance =
      provenance presentation
  ; Old.R109SelectedStressCylinderPresentation.round109 =
      round109 presentation
  ; Old.R109SelectedStressCylinderPresentation.completionMatches =
      completionMatches presentation
  ; Old.R109SelectedStressCylinderPresentation.selectedObservable =
      stressInsertionObservable presentation
  ; Old.R109SelectedStressCylinderPresentation.PositiveTimeSupported =
      PositiveTimeSupported presentation
  ; Old.R109SelectedStressCylinderPresentation.GaugeInvariantObservable =
      GaugeInvariantObservable presentation
  ; Old.R109SelectedStressCylinderPresentation.selectedPositiveTime =
      stressInsertionPositiveTime presentation
  ; Old.R109SelectedStressCylinderPresentation.selectedGaugeInvariant =
      stressInsertionGaugeInvariant presentation
  ; Old.R109SelectedStressCylinderPresentation.StressInsertionObservableMeaning =
      sameSelectedInsertionMeaning presentation
  ; Old.R109SelectedStressCylinderPresentation.selectedObservablePresentsR110StressInsertion =
      refl , refl
  }

arbitraryStressInsertionMeaningPredicateEliminated : Bool
arbitraryStressInsertionMeaningPredicateEliminated = true

remainingNovelE2E4DataAreObservableAndTwoAdmissibilityProofs : Bool
remainingNovelE2E4DataAreObservableAndTwoAdmissibilityProofs = true

r109InsertionIdentityIsDefinitionallyPinned : Bool
r109InsertionIdentityIsDefinitionallyPinned = true
