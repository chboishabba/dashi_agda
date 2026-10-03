{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationExact where

------------------------------------------------------------------------
-- TERMINAL SHARED E2/E4 PRODUCER:
-- R110 FINITE STRESS INSERTION -> ONE SELECTED REAL CYLINDER OBSERVABLE.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Product using (_×_; _,_)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ)

import DASHI.Physics.Foundations.CMP119CosmologySelectedLocalCStressCylinderExact as Selected
import DASHI.Physics.YangMills.BalabanCMP119CompatibleLocalExpectationFlowExact as Source
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119Round109ConcreteLocalCExact as Round109

record R109SelectedStressCylinderPresentation
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
      Round109.Round109ConcreteLocalCStressWeld
        Y group localC

    completionMatches :
      R110.markedCompletion provenance
      ≡ Round109.completion round109

    selectedObservable : Configuration → ℝ

    PositiveTimeSupported : (Configuration → ℝ) → Set
    GaugeInvariantObservable : (Configuration → ℝ) → Set

    selectedPositiveTime : PositiveTimeSupported selectedObservable
    selectedGaugeInvariant : GaugeInvariantObservable selectedObservable

    -- Exact remaining finite-presentation seam.  Its left endpoint is not the
    -- whole Cauchy package but the literal selected R109 insertion pair.
    StressInsertionObservableMeaning :
      Source.SourceNativeOrdinaryCharacteristicPair
        (R109.source (R110.sourceCauchy provenance)) →
      (Configuration → ℝ) → Set

    selectedObservablePresentsR110StressInsertion :
      StressInsertionObservableMeaning
        (R109.stressInsertion (R110.sourceCauchy provenance))
        selectedObservable

open R109SelectedStressCylinderPresentation public

asSelectedLocalCStressCylinder :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC} →
  R109SelectedStressCylinderPresentation
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
  Selected.SelectedLocalCStressCylinder
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
asSelectedLocalCStressCylinder {localC = localC} presentation = record
  { Selected.SelectedLocalCStressCylinder.selectedObservable =
      selectedObservable presentation
  ; Selected.SelectedLocalCStressCylinder.PositiveTimeSupported =
      PositiveTimeSupported presentation
  ; Selected.SelectedLocalCStressCylinder.GaugeInvariantObservable =
      GaugeInvariantObservable presentation
  ; Selected.SelectedLocalCStressCylinder.selectedPositiveTime =
      selectedPositiveTime presentation
  ; Selected.SelectedLocalCStressCylinder.selectedGaugeInvariant =
      selectedGaugeInvariant presentation
  ; Selected.SelectedLocalCStressCylinder.SelectedStressObservableMeaning =
      λ stress observable →
        (stress ≡ LocalC.stressTensor localC)
        × StressInsertionObservableMeaning presentation
            (R109.stressInsertion
              (R110.sourceCauchy (provenance presentation))) observable
  ; Selected.SelectedLocalCStressCylinder.selectedObservableMeansLocalCStress =
      refl , selectedObservablePresentsR110StressInsertion presentation
  }

sameCompletionEndpointAlreadyCarriesLocalCIdentity :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (presentation :
      R109SelectedStressCylinderPresentation
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
  Top.stressTensor Y group ≡ LocalC.stressTensor localC
sameCompletionEndpointAlreadyCarriesLocalCIdentity presentation =
  Round109.literalClayStressIsConcreteLocalCStress (round109 presentation)

allStressEncodingFamilyEliminated : Bool
allStressEncodingFamilyEliminated = true

remainingE2E4NovelProducerIsExactR109InsertionPresentation : Bool
remainingE2E4NovelProducerIsExactR109InsertionPresentation = true

continuumStressIdentityIsNotASecondE2E4Leaf : Bool
continuumStressIdentityIsNotASecondE2E4Leaf = true
