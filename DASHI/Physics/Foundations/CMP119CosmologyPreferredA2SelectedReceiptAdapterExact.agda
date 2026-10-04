{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyPreferredA2SelectedReceiptAdapterExact where

------------------------------------------------------------------------
-- A2 ADAPTER ELIMINATION.
--
-- Once the one selected R109 stress-cylinder presentation exists, the exact
-- preferred typed A2 receipt is pure structure: same selected observable,
-- same externally fixed insertion-meaning relation, and the same published
-- Wilson positive-time / gauge-invariance proofs.  No second physical choice
-- or proof is charged here.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)

import DASHI.Physics.Foundations.CMP119CosmologyFiveSourcePhysicsTypedReceiptsExact as Typed
import DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationExact as Selected
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC

asExactPreferredA2Receipt :
  ∀ {C S Y group
      G X Configuration Position CurvaturePolynomial LocalOperator
      OPECoefficient Hilbert Vector Hamiltonian Algebra
      Scale Volume Root ContinuumFamily Core
      sequenceLimit limitLaws quotient division osS osInputs reconstruction
      localC}
    (presentation :
      Selected.R109SelectedStressCylinderPresentation
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
  Typed.A2SelectedR109WilsonAdmissibleInsertionReceipt
    (R110.sourceCauchy (Selected.provenance presentation))
    Configuration
    (Selected.StressInsertionObservableMeaning presentation)
    (Selected.publishedOS presentation)
asExactPreferredA2Receipt presentation = record
  { Typed.A2SelectedR109WilsonAdmissibleInsertionReceipt.exactSelectedObservable =
      Selected.selectedObservable presentation
  ; Typed.A2SelectedR109WilsonAdmissibleInsertionReceipt.exactSelectedInsertionHasMeaning =
      Selected.selectedObservablePresentsR110StressInsertion presentation
  ; Typed.A2SelectedR109WilsonAdmissibleInsertionReceipt.exactSelectedPositiveTime =
      Selected.selectedPositiveTime presentation
  ; Typed.A2SelectedR109WilsonAdmissibleInsertionReceipt.exactSelectedGaugeInvariant =
      Selected.selectedGaugeInvariant presentation
  }

a2SelectedPresentationToTypedReceiptIsCompilerOnly : Bool
a2SelectedPresentationToTypedReceiptIsCompilerOnly = true

a2AdapterAddsNoSecondObservableChoice : Bool
a2AdapterAddsNoSecondObservableChoice = true

a2AdapterAddsNoSecondAdmissibilityProof : Bool
a2AdapterAddsNoSecondAdmissibilityProof = true
