module DASHI.Physics.YangMills.BalabanCMP122Equation171Gate4ContributionQuadratureExact where

------------------------------------------------------------------------
-- LITERAL CMP122 EQ.(1.71) -> EXECUTABLE GATE4 FINITE CONTRIBUTIONS
--
-- Corrected semantics:
--   Gate4 rational activity is interpreted as an approximation to the WHOLE
--   Haar-weighted source-cell contribution, not as an exact copy of the bare
--   transcendental Eq.(1.71) density.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

open import DASHI.Foundations.RealAnalysisAxioms using
  (ℝ; 1ℝ; absℝ; _-ℝ_; _*ℝ_; _≤ℝ_)
import Data.Rational.Base as Rational using (ℚ)
open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanA2RationalSensitivityToRealContractionRound104Exact as AddEmbed
import DASHI.Physics.YangMills.BalabanRationalBetaCertificateToRealSlopeRound102Exact as BaseEmbed
import DASHI.Physics.YangMills.BalabanFederbushRationalMatrixRealImageRound208Exact as RingEmbed
import DASHI.Physics.YangMills.BalabanClayP3FiniteConstrainedIntegralExact as Integral
import DASHI.Physics.YangMills.BalabanClayGate4ComponentClassAndFiniteTOperationExact as T
import DASHI.Physics.YangMills.BalabanClayGate4CanonicalRationalPhysicalTExact as PhysicalT
import DASHI.Physics.YangMills.BalabanCMP122Equation171TOperationSemanticsExact as Eq171
import DASHI.Physics.YangMills.BalabanEmbeddedCanonicalRationalConstrainedFoldExact as Embedded
import DASHI.Physics.YangMills.BalabanCompactHaarMassExactContributionApproximationExact as Approx

embedQ :
  RingEmbed.RationalRealRingEmbedding → ℚ → ℝ
embedQ embedding =
  BaseEmbed.embed
    (AddEmbed.base (RingEmbed.additive embedding))

record Equation171Gate4ContributionQuadrature
    {Scale Fine SlowField Component Functional : Set}
    (construction :
      PhysicalT.CanonicalRationalPhysicalTConstruction
        Scale Fine SlowField Component Functional)
    (source :
      Eq171.CMP122Equation171TOperationSemantics Fine SlowField)
    (embedding :
      RingEmbed.RationalRealRingEmbedding) : Set₁ where
  field
    scaleAt : Nat → Scale

    selectedAt : ∀ cutoff →
      T.SecondClassComponent
        (T.classData (PhysicalT.canonicalPhysicalTData construction))
        (scaleAt cutoff)

    fieldsAt : Nat → SlowField → List Fine

    fieldsAreGate4FastFibre :
      ∀ cutoff slow →
      fieldsAt cutoff slow
      ≡
      T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt cutoff)
        (T.component (selectedAt cutoff))

    sourceCellIntegral :
      Nat → SlowField → Fine → ℝ

    sourceCellMass :
      Nat → SlowField → Fine → ℝ

    sourceSample :
      Nat → SlowField → Fine → ℝ

    oscillationModulus :
      Nat → SlowField → ℝ

    contributionApproximationModulus :
      Nat → SlowField → ℝ

    sourceCellsSumToEquation171Integral :
      ∀ cutoff slow →
      RingEmbed.realSum
        (fieldsAt cutoff slow)
        (sourceCellIntegral cutoff slow)
      ≡
      Eq171.equation171ConstrainedIntegral source cutoff slow
        (Eq171.equation171ExponentialDensity source cutoff slow)

    sourceCellMassesSumOne :
      ∀ cutoff slow →
      RingEmbed.realSum
        (fieldsAt cutoff slow)
        (sourceCellMass cutoff slow)
      ≡
      1ℝ

    sourceCellOscillationBound :
      ∀ cutoff slow fine →
      absℝ
        (sourceCellIntegral cutoff slow fine
          -ℝ
          (sourceCellMass cutoff slow fine
            *ℝ
            sourceSample cutoff slow fine))
      ≤ℝ
      (sourceCellMass cutoff slow fine
        *ℝ
        oscillationModulus cutoff slow)

    gate4ContributionApproximationBound :
      ∀ cutoff slow fine →
      absℝ
        ((sourceCellMass cutoff slow fine
            *ℝ
            sourceSample cutoff slow fine)
          -ℝ
          embedQ embedding
            (Integral.selectedWith
              (T.sumData (PhysicalT.canonicalPhysicalTData construction))
              (T.localIntegrand
                (PhysicalT.canonicalPhysicalTData construction)
                (scaleAt cutoff)
                (T.component (selectedAt cutoff))
                slow
                (T.oneFunctional
                  (PhysicalT.canonicalPhysicalTData construction)))
              slow fine))
      ≤ℝ
      (sourceCellMass cutoff slow fine
        *ℝ
        contributionApproximationModulus cutoff slow)

open Equation171Gate4ContributionQuadrature public

asContributionApproximation :
  ∀ {Scale Fine SlowField Component Functional construction source embedding}
    (dataSet :
      Equation171Gate4ContributionQuadrature
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        construction source embedding)
    cutoff slow →
  Approx.MassExactContributionApproximation Fine
asContributionApproximation
  {construction = construction} {embedding = embedding}
  dataSet cutoff slow = record
  { Approx.MassExactContributionApproximation.cells =
      fieldsAt dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.sourceCellIntegral =
      sourceCellIntegral dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.cellMass =
      sourceCellMass dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.sourceSample =
      sourceSample dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.executableContribution =
      λ fine →
        embedQ embedding
          (Integral.selectedWith
            (T.sumData (PhysicalT.canonicalPhysicalTData construction))
            (T.localIntegrand
              (PhysicalT.canonicalPhysicalTData construction)
              (scaleAt dataSet cutoff)
              (T.component (selectedAt dataSet cutoff))
              slow
              (T.oneFunctional
                (PhysicalT.canonicalPhysicalTData construction)))
            slow fine)
  ; Approx.MassExactContributionApproximation.oscillationModulus =
      oscillationModulus dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.contributionApproximationModulus =
      contributionApproximationModulus dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.cellOscillationBound =
      sourceCellOscillationBound dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.cellContributionApproximationBound =
      gate4ContributionApproximationBound dataSet cutoff slow
  ; Approx.MassExactContributionApproximation.massesSumOne =
      sourceCellMassesSumOne dataSet cutoff slow
  }

sourceIntegralIsApproximationSource :
  ∀ {Scale Fine SlowField Component Functional construction source embedding}
    (dataSet :
      Equation171Gate4ContributionQuadrature
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        construction source embedding)
    cutoff slow →
  Approx.sourceIntegral
    (asContributionApproximation dataSet cutoff slow)
  ≡
  Eq171.equation171ConstrainedIntegral source cutoff slow
    (Eq171.equation171ExponentialDensity source cutoff slow)
sourceIntegralIsApproximationSource dataSet cutoff slow =
  sourceCellsSumToEquation171Integral dataSet cutoff slow

executableSumIsEmbeddedGate4Mass :
  ∀ {Scale Fine SlowField Component Functional construction source embedding}
    (dataSet :
      Equation171Gate4ContributionQuadrature
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        construction source embedding)
    cutoff slow →
  Approx.executableSum
    (asContributionApproximation dataSet cutoff slow)
  ≡
  embedQ embedding
    (T.localizedTOperation
      (PhysicalT.canonicalPhysicalTData construction)
      (scaleAt dataSet cutoff)
      (selectedAt dataSet cutoff)
      slow
      (T.oneFunctional
        (PhysicalT.canonicalPhysicalTData construction)))
executableSumIsEmbeddedGate4Mass
  {construction = construction} {embedding = embedding}
  dataSet cutoff slow
  rewrite fieldsAreGate4FastFibre dataSet cutoff slow =
  sym
    (Embedded.embeddedConstrainedIntegralExact
      embedding
      (PhysicalT.sumCarrier construction)
      (T.fastFibre
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt dataSet cutoff)
        (T.component (selectedAt dataSet cutoff)))
      (T.localIntegrand
        (PhysicalT.canonicalPhysicalTData construction)
        (scaleAt dataSet cutoff)
        (T.component (selectedAt dataSet cutoff))
        slow
        (T.oneFunctional
          (PhysicalT.canonicalPhysicalTData construction)))
      slow)

equation171ToEmbeddedGate4ErrorBound :
  ∀ {Scale Fine SlowField Component Functional construction source embedding}
    (dataSet :
      Equation171Gate4ContributionQuadrature
        {Scale = Scale} {Fine = Fine} {SlowField = SlowField}
        {Component = Component} {Functional = Functional}
        construction source embedding)
    cutoff slow →
  absℝ
    (Eq171.equation171ConstrainedIntegral source cutoff slow
      (Eq171.equation171ExponentialDensity source cutoff slow)
      -ℝ
      embedQ embedding
        (T.localizedTOperation
          (PhysicalT.canonicalPhysicalTData construction)
          (scaleAt dataSet cutoff)
          (selectedAt dataSet cutoff)
          slow
          (T.oneFunctional
            (PhysicalT.canonicalPhysicalTData construction))))
  ≤ℝ
  Approx.combinedModulus
    (asContributionApproximation dataSet cutoff slow)
equation171ToEmbeddedGate4ErrorBound
  {construction = construction} {embedding = embedding}
  dataSet cutoff slow =
  subst
    (λ sourceValue →
      absℝ
        (sourceValue
          -ℝ
          embedQ embedding
            (T.localizedTOperation
              (PhysicalT.canonicalPhysicalTData construction)
              (scaleAt dataSet cutoff)
              (selectedAt dataSet cutoff)
              slow
              (T.oneFunctional
                (PhysicalT.canonicalPhysicalTData construction))))
      ≤ℝ
      Approx.combinedModulus
        (asContributionApproximation dataSet cutoff slow))
    (sourceIntegralIsApproximationSource dataSet cutoff slow)
    (subst
      (λ executableValue →
        absℝ
          (Approx.sourceIntegral
            (asContributionApproximation dataSet cutoff slow)
            -ℝ executableValue)
        ≤ℝ
        Approx.combinedModulus
          (asContributionApproximation dataSet cutoff slow))
      (executableSumIsEmbeddedGate4Mass dataSet cutoff slow)
      (Approx.massExactContributionApproximationError
        (asContributionApproximation dataSet cutoff slow)))

equation171Gate4ContributionQuadratureCompilerLevel : ProofLevel
equation171Gate4ContributionQuadratureCompilerLevel = machineChecked

equation171Gate4ContributionErrorBoundLevel : ProofLevel
equation171Gate4ContributionErrorBoundLevel = machineChecked

-- Remaining literal/source analysis:
-- build shrinking Haar cells and prove both moduli vanish.
literalEquation171CellPartitionAndOscillationLevel : ProofLevel
literalEquation171CellPartitionAndOscillationLevel = conditional

literalGate4WeightedContributionApproximationLevel : ProofLevel
literalGate4WeightedContributionApproximationLevel = conditional
