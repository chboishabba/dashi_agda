{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedR109FiniteExpectationFromSelectedPresentationExact where

------------------------------------------------------------------------
-- A2 -> B1 CONSUMER WITHOUT A GLOBAL PAIR EVALUATOR.
--
-- The selected R109 stress presentation already supplies exactly the one real
-- cylinder observable consumed by the cosmology path.  Evaluate that observable
-- on the same pinned finite OS family and use the same R110/R109 provenance for
-- the explicit tail.  No `pair -> observable` function is needed downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)
open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyR109SelectedStressCylinderPresentationExact as Selected
import DASHI.Physics.Foundations.CMP119CosmologyR144R109ExpectationCompletionMaxCutExact as Tail
import DASHI.Physics.YangMills.BalabanSameFamilyStressCauchySchwingerRound109Exact as R109
import DASHI.Physics.YangMills.BalabanStressSameObjectProvenanceRound110Exact as R110
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as Embed
import DASHI.Physics.YangMills.YangMillsFinitePhysicalMeasureLimitExact as Limit
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119OSSystemExact as A
import DASHI.Physics.YangMills.YangMillsClayPinnedCMP119ConcreteLocalCExact as LocalC
import DASHI.Physics.YangMills.YangMillsClayLiteralTopDownConstructionExact as Top
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
import DASHI.Physics.YangMills.BalabanCanonicalRealLimitAlgebraExact as RealLimit
import DASHI.Physics.YangMills.BalabanNormalizedExpectationConvergenceExact as Quotient
import DASHI.Physics.YangMills.BalabanNormalizedCylinderExpectationLimitExact as Division

module _
    {C : Top.LiteralYangMillsCarriers}
    {S : Top.LiteralYangMillsSemantics C}
    (Y : Top.LiteralYangMillsConstruction C S)
    (group : Top.CompactSimpleGroup C)
    {G X Configuration Position CurvaturePolynomial LocalOperator
     OPECoefficient Hilbert Vector Hamiltonian Algebra
     Scale Volume Root ContinuumFamily Core
     sequenceLimit limitLaws quotient division osS
     osInputs reconstruction}
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
        localC)
    (embedding : Embed.OrderedRationalRealEmbedding)
  where

  source : R109.SourceNativeStressScaleCauchy
  source = R110.sourceCauchy (Selected.provenance presentation)

  selectedObservable : Configuration → ℝ
  selectedObservable = Selected.selectedObservable presentation

  selectedFiniteExpectation : Nat → ℝ
  selectedFiniteExpectation cutoff =
    Limit.finiteExpectation (A.family osInputs group) cutoff selectedObservable

  embeddedR109Tail : Nat → ℝ
  embeddedR109Tail cutoff =
    Embed.embed embedding (Tail.r109RemainingTail source cutoff)

  record SelectedPresentationR109RealCompletion
      (completedRationalExpectation : ℚ) : Set₁ where
    field
      completionUpperTail : ∀ cutoff →
        Embed.embed embedding completedRationalExpectation
        ≤ℝ selectedFiniteExpectation cutoff +ℝ embeddedR109Tail cutoff

  open SelectedPresentationR109RealCompletion public

  selectedFiniteExpectationIsPinnedFamilyExpectation : ∀ cutoff →
    selectedFiniteExpectation cutoff
    ≡ Limit.finiteExpectation
        (A.family osInputs group) cutoff
        (Selected.selectedObservable presentation)
  selectedFiniteExpectationIsPinnedFamilyExpectation cutoff = refl

finiteExpectationConsumerNeedsFunctionalPairEvaluator : Bool
finiteExpectationConsumerNeedsFunctionalPairEvaluator = false

finiteExpectationStillUsesPinnedOSFamily : Bool
finiteExpectationStillUsesPinnedOSFamily = true

selectedInsertionSemanticsIsSufficientForFiniteExpectationConsumer : Bool
selectedInsertionSemanticsIsSufficientForFiniteExpectationConsumer = true
