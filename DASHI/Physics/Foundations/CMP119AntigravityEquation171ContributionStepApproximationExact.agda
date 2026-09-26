{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119AntigravityEquation171ContributionStepApproximationExact where

open import Agda.Builtin.Nat using (Nat)
open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 0ℝ; absℝ; _-ℝ_; _≤ℝ_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.YangMills.BalabanCMP119Equation218FactorizedFunctionalDensityExact as Factor
import DASHI.Physics.YangMills.BalabanCMP119FactorizedDensityApproximationExact as Approx
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionRefinementLimitExact as Contribution
import DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionQuadratureExact as Quad
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactContributionApproximationExact as CellApprox
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanRealSequenceLimitByVanishingErrorExact as Seq
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- CORRECTED CMP119 ONE-STEP ADAPTER
--
-- Source one-step value = Eq.(1.71) source T-mass, while each executable
-- approximation is the embedded Gate4 WHOLE-CELL contribution quadrature.
-- The marked error is the sum of
--
--   cell oscillation modulus
--   + executable weighted-contribution approximation modulus.
--
-- No exact bare source-density = rational Gate4 activity premise is used.
------------------------------------------------------------------------

record CMP119Equation171ContributionStepApproximation
    {trajectory split SlowField Sequence Component Step}
    (factorized :
      Factor.CMP119Equation218FactorizedFunctionalData
        {trajectory = trajectory} {split = split}
        SlowField Sequence Component Step)
    {Scale Fine FunctionalValue : Set}
    (embedding : RingEmbed.RationalRealRingEmbedding)
    (sequenceLimit : Seq.RealSequenceLimitByVanishingError) : Set₂ where
  field
    sourceTAt :
      Sequence → Component → Step →
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField

    contributionAt :
      (sequence : Sequence) →
      (component : Component) →
      (step : Step) →
      Contribution.Equation171Gate4ContributionRefinementLimit
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = FunctionalValue}
        (sourceTAt sequence component step) embedding sequenceLimit

    sourceStepIsEquation171Mass :
      ∀ scale sequence component step slow →
      Factor.oneStepValue factorized
        scale sequence component step slow
      ≡
      Eq171.sourceTOperationMass
        (sourceTAt sequence component step)
        scale slow

    ordinaryMajorant :
      Nat → Sequence → Component → Step → SlowField → ℝ

    ordinaryNonnegative :
      ∀ scale sequence component step slow →
      0ℝ ≤ℝ ordinaryMajorant scale sequence component step slow

    sourceStepBound :
      ∀ scale sequence component step slow →
      absℝ (Factor.oneStepValue factorized
        scale sequence component step slow)
      ≤ℝ ordinaryMajorant scale sequence component step slow

    approximateStepBound :
      ∀ refinement scale sequence component step slow →
      absℝ
        (Contribution.embeddedGate4MassAt
          (contributionAt sequence component step)
          refinement scale slow)
      ≤ℝ ordinaryMajorant scale sequence component step slow

    residualMajorant :
      Nat → Sequence → SlowField → ℝ

    residualMajorantNonnegative :
      ∀ scale sequence slow →
      0ℝ ≤ℝ residualMajorant scale sequence slow

    residualBound :
      ∀ scale sequence slow →
      absℝ (Factor.sequenceResidual factorized scale sequence slow)
      ≤ℝ residualMajorant scale sequence slow

open CMP119Equation171ContributionStepApproximation public

markedMajorant :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit} →
  CMP119Equation171ContributionStepApproximation
    {trajectory = trajectory} {split = split}
    {SlowField = SlowField} {Sequence = Sequence}
    {Component = Component} {Step = Step}
    factorized
    {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
    embedding sequenceLimit →
  Nat → Nat → Sequence → Component → Step → SlowField → ℝ
markedMajorant dataSet refinement scale sequence component step slow =
  CellApprox.combinedModulus
    (Quad.asContributionApproximation
      (Contribution.quadratureAt
        (contributionAt dataSet sequence component step)
        refinement)
      scale slow)

markedMajorantVanishes :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      CMP119Equation171ContributionStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = Step}
        factorized
        {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    scale sequence component step slow →
  Seq.Vanishes sequenceLimit
    (λ refinement →
      markedMajorant dataSet refinement scale sequence component step slow)
markedMajorantVanishes dataSet scale sequence component step slow =
  Contribution.combinedModulusVanishes
    (contributionAt dataSet sequence component step)
    scale slow

stepDifferenceBound :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      CMP119Equation171ContributionStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = Step}
        factorized
        {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
        embedding sequenceLimit)
    refinement scale sequence component step slow →
  absℝ
    (Factor.oneStepValue factorized
      scale sequence component step slow
      -ℝ
     Contribution.embeddedGate4MassAt
       (contributionAt dataSet sequence component step)
       refinement scale slow)
  ≤ℝ
  markedMajorant
    dataSet refinement scale sequence component step slow
stepDifferenceBound dataSet refinement scale sequence component step slow =
  let
    sourceT = sourceTAt dataSet sequence component step
    contribution = contributionAt dataSet sequence component step
    quadrature = Contribution.quadratureAt contribution refinement

    raw =
      Quad.equation171ToEmbeddedGate4ErrorBound
        quadrature scale slow

    sourceStepIsIntegral :
      Factor.oneStepValue factorized
        scale sequence component step slow
      ≡
      Eq171.equation171ConstrainedIntegral sourceT scale slow
        (Eq171.equation171ExponentialDensity sourceT scale slow)
    sourceStepIsIntegral =
      trans
        (sourceStepIsEquation171Mass
          dataSet scale sequence component step slow)
        (Eq171.equation171DefinesTOperationMass sourceT scale slow)
  in
  subst
    (λ sourceValue →
      absℝ
        (sourceValue -ℝ
          Contribution.embeddedGate4MassAt
            contribution refinement scale slow)
      ≤ℝ
      markedMajorant
        dataSet refinement scale sequence component step slow)
    (sym sourceStepIsIntegral)
    raw

-- The generic factorized compiler also asks for marked nonnegativity.  Rather
-- than invent it from a vanishing statement, keep it as one explicit local
-- scalar property on the two physical moduli.
record ContributionMarkedNonnegative
    {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      CMP119Equation171ContributionStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = Step}
        factorized
        {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
        embedding sequenceLimit) : Set₁ where
  field
    markedNonnegative :
      ∀ refinement scale sequence component step slow →
      0ℝ ≤ℝ
      markedMajorant dataSet
        refinement scale sequence component step slow

open ContributionMarkedNonnegative public

asFactorizedDensityApproximation :
  ∀ {trajectory split SlowField Sequence Component Step factorized
      Scale Fine FunctionalValue embedding sequenceLimit}
    (dataSet :
      CMP119Equation171ContributionStepApproximation
        {trajectory = trajectory} {split = split}
        {SlowField = SlowField} {Sequence = Sequence}
        {Component = Component} {Step = Step}
        factorized
        {Scale = Scale} {Fine = Fine} {FunctionalValue = FunctionalValue}
        embedding sequenceLimit) →
    ContributionMarkedNonnegative dataSet →
  Approx.CMP119FactorizedDensityApproximation
    SlowField Sequence Component Step
asFactorizedDensityApproximation
    {factorized = factorized}
    dataSet marked = record
  { Approx.CMP119FactorizedDensityApproximation.admissibleSequences =
      Factor.admissibleSequences factorized
  ; Approx.CMP119FactorizedDensityApproximation.componentsAt =
      Factor.componentsAt factorized
  ; Approx.CMP119FactorizedDensityApproximation.orderedStepsAt =
      Factor.orderedStepsAt factorized
  ; Approx.CMP119FactorizedDensityApproximation.sourceStep =
      Factor.oneStepValue factorized
  ; Approx.CMP119FactorizedDensityApproximation.approximateStep =
      λ refinement scale sequence component step slow →
        Contribution.embeddedGate4MassAt
          (contributionAt dataSet sequence component step)
          refinement scale slow
  ; Approx.CMP119FactorizedDensityApproximation.ordinaryMajorant =
      ordinaryMajorant dataSet
  ; Approx.CMP119FactorizedDensityApproximation.markedMajorant =
      markedMajorant dataSet
  ; Approx.CMP119FactorizedDensityApproximation.residualFactor =
      Factor.sequenceResidual factorized
  ; Approx.CMP119FactorizedDensityApproximation.residualMajorant =
      residualMajorant dataSet
  ; Approx.CMP119FactorizedDensityApproximation.ordinaryNonnegative =
      ordinaryNonnegative dataSet
  ; Approx.CMP119FactorizedDensityApproximation.markedNonnegative =
      markedNonnegative marked
  ; Approx.CMP119FactorizedDensityApproximation.sourceStepBound =
      sourceStepBound dataSet
  ; Approx.CMP119FactorizedDensityApproximation.approximateStepBound =
      approximateStepBound dataSet
  ; Approx.CMP119FactorizedDensityApproximation.stepDifferenceBound =
      stepDifferenceBound dataSet
  ; Approx.CMP119FactorizedDensityApproximation.residualMajorantNonnegative =
      residualMajorantNonnegative dataSet
  ; Approx.CMP119FactorizedDensityApproximation.residualBound =
      residualBound dataSet
  }

cmp119ContributionStepErrorCompilerLevel : ProofLevel
cmp119ContributionStepErrorCompilerLevel = machineChecked

exactBareDensityGate4EqualityRequired : Agda.Builtin.Bool.Bool
exactBareDensityGate4EqualityRequired = Agda.Builtin.Bool.false
