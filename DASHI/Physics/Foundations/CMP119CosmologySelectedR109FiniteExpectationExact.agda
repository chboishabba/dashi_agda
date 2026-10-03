{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologySelectedR109FiniteExpectationExact where

------------------------------------------------------------------------
-- B1 SAME-FAMILY ENDPOINT SEQUENCE.
--
-- Once E2 presents the literal Round109 stress insertion as a real cylinder
-- observable, the pinned OS input already supplies the finite normalized family
-- on which that observable is evaluated.  Therefore the finite endpoint
-- sequence has NO independent family and NO independent observable choice:
--
--   F_k = finiteExpectation (family osInputs group) k selectedStressObservable.
--
-- The only remaining completion theorem is quantitative comparison of a
-- selected completed rational response with this exact real sequence plus the
-- embedded Round109 tail.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base as ℚ using (ℚ)

open import DASHI.Foundations.RealAnalysisAxioms using (ℝ; _+ℝ_; _≤ℝ_)

import DASHI.Physics.Foundations.CMP119CosmologyR109FunctionalStressCylinderPresentationExact as Presentation
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
     sequenceLimit limitLaws quotient division
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
        {S = S}
        osInputs reconstruction group)
    (presentation :
      Presentation.FunctionalR109StressCylinderPresentation
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
        {osS = S} {osInputs = osInputs} {reconstruction = reconstruction}
        localC)
    (embedding : Embed.OrderedRationalRealEmbedding)
  where

  source : R109.SourceNativeStressScaleCauchy
  source = R110.sourceCauchy (Presentation.provenance presentation)

  selectedObservable : Configuration → ℝ
  selectedObservable = Presentation.selectedStressObservable presentation

  selectedFiniteExpectation : Nat → ℝ
  selectedFiniteExpectation cutoff =
    Limit.finiteExpectation (A.family osInputs group) cutoff selectedObservable

  embeddedR109Tail : Nat → ℝ
  embeddedR109Tail cutoff =
    Embed.embed embedding (Tail.r109RemainingTail source cutoff)

  record SelectedR109ConcreteRealCompletion
      (completedRationalExpectation : ℚ) : Set₁ where
    field
      completionUpperTail : ∀ cutoff →
        Embed.embed embedding completedRationalExpectation
        ≤ℝ selectedFiniteExpectation cutoff +ℝ embeddedR109Tail cutoff

  open SelectedR109ConcreteRealCompletion public

  selectedFiniteExpectationIsPinnedFamilyExpectation : ∀ cutoff →
    selectedFiniteExpectation cutoff
    ≡ Limit.finiteExpectation
        (A.family osInputs group) cutoff
        (Presentation.selectedStressObservable presentation)
  selectedFiniteExpectationIsPinnedFamilyExpectation cutoff = refl

  noIndependentFiniteFamilyOrObservableChoice : Bool
  noIndependentFiniteFamilyOrObservableChoice = true

  remainingB1ContentIsSameR109CompletionBoundOnPinnedFiniteExpectations : Bool
  remainingB1ContentIsSameR109CompletionBoundOnPinnedFiniteExpectations = true
