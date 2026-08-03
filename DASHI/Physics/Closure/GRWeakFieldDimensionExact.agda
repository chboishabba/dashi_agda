module DASHI.Physics.Closure.GRWeakFieldDimensionExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Albert Einstein.
-- Title: "Die Grundlage der allgemeinen Relativitaetstheorie".
-- Annalen der Physik 354 (1916), 769--822.
-- DOI: 10.1002/andp.19163540702.
--
-- Author: Juergen Ehlers.
-- Title: "On the Newtonian Limit of Einstein's Theory of Gravitation".
-- General Relativity and Gravitation 51 (2019), article 163
-- (English republication of the 1981 frame-theory article).
-- DOI: 10.1007/s10714-019-2624-0.
--
-- PURPOSE
-- Fix the weak-field sign convention against the repository's existing flat
-- 1+3 carrier, prove the dimensional compatibility Phi ~ c^2, and expose the
-- full five-step imported-analysis cutset required before Einstein's equation
-- may be reduced to the Newtonian Poisson equation.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

import DASHI.Geometry.FlatLorentzianModel as Flat
import DASHI.Physics.Units.MechanicalDimensionExact as Dimension
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Signature convention.  The existing flat carrier has negative timelike and
-- positive spacelike diagonal entries, so the selected convention is
-- mostly-plus (-,+,+,+).
------------------------------------------------------------------------

data MetricSignatureConvention : Set where
  mostlyPlus : MetricSignatureConvention
  mostlyMinus : MetricSignatureConvention

selectedMetricSignature : MetricSignatureConvention
selectedMetricSignature = mostlyPlus

repositoryTimeAxisUsesNegativeSlot :
  Flat.signature13 Flat.timeAxis ≡ Flat.timelikeSign
repositoryTimeAxisUsesNegativeSlot = Flat.timeIsTimelike

selectedSignatureMatchesRepository :
  selectedMetricSignature ≡ mostlyPlus
selectedSignatureMatchesRepository = refl

------------------------------------------------------------------------
-- Dimension theorem.
------------------------------------------------------------------------

newtonianPotentialHasSpeedSquaredDimension :
  Dimension.newtonianPotentialDimension
  ≡ Dimension.speedSquaredDimension
newtonianPotentialHasSpeedSquaredDimension =
  Dimension.potentialMatchesSpeedSquared

record WeakFieldScalarModel : Set₁ where
  field
    Scalar : Set
    zero one two : Scalar
    _+_ _*_ : Scalar → Scalar → Scalar
    negate divide : Scalar → Scalar → Scalar

    potential :
      Dimension.Quantity Scalar Dimension.newtonianPotentialDimension

    lightSpeedSquared :
      Dimension.Quantity Scalar Dimension.speedSquaredDimension

    potentialOverLightSpeedSquared :
      Dimension.Quantity Scalar Dimension.dimensionless

    ratioMeaning :
      Dimension.magnitude potentialOverLightSpeedSquared
      ≡ divide
          (Dimension.magnitude potential)
          (Dimension.magnitude lightSpeedSquared)

    metric00 : Scalar

    -- Mostly-plus convention with an attractive Newtonian potential Phi < 0:
    -- g_00 = -(1 + 2 Phi/c^2).
    metric00Meaning :
      metric00
      ≡ negate one
          (one +
            (two * Dimension.magnitude potentialOverLightSpeedSquared))

open WeakFieldScalarModel public

------------------------------------------------------------------------
-- The Newtonian limit is not one unnamed "weak-field assumption".  The source
-- proof must identify each transformation in the standard chain.
------------------------------------------------------------------------

record LinearizedEinsteinPoissonHypotheses
    (model : WeakFieldScalarModel) : Set₁ where
  field
    WeakMetricPerturbation : Set
    weakMetricPerturbation : WeakMetricPerturbation

    TraceReversedLinearization : Set
    traceReversedLinearization : TraceReversedLinearization

    HarmonicGaugeCondition : Set
    harmonicGaugeCondition : HarmonicGaugeCondition

    StaticFieldReduction : Set
    staticFieldReduction : StaticFieldReduction

    NonRelativistic00SourceIdentification : Set
    nonRelativistic00SourceIdentification :
      NonRelativistic00SourceIdentification

open LinearizedEinsteinPoissonHypotheses public

record NewtonianPoissonLimitAuthority
    (model : WeakFieldScalarModel)
    (hypotheses : LinearizedEinsteinPoissonHypotheses model) : Set₁ where
  field
    LaplacianPotential : Set
    MassDensitySource : Set
    Einstein00ReducesToPoisson : Set

    poissonLimitImported :
      WeakMetricPerturbation hypotheses →
      TraceReversedLinearization hypotheses →
      HarmonicGaugeCondition hypotheses →
      StaticFieldReduction hypotheses →
      NonRelativistic00SourceIdentification hypotheses →
      Einstein00ReducesToPoisson

open NewtonianPoissonLimitAuthority public

selectedPoissonLimit :
  ∀ {model hypotheses} →
  (authority : NewtonianPoissonLimitAuthority model hypotheses) →
  Einstein00ReducesToPoisson authority
selectedPoissonLimit {hypotheses = hypotheses} authority =
  poissonLimitImported authority
    (weakMetricPerturbation hypotheses)
    (traceReversedLinearization hypotheses)
    (harmonicGaugeCondition hypotheses)
    (staticFieldReduction hypotheses)
    (nonRelativistic00SourceIdentification hypotheses)

weakFieldDimensionTheoremLevel : ProofLevel
weakFieldDimensionTheoremLevel = machineChecked

metricSignatureSelectionLevel : ProofLevel
metricSignatureSelectionLevel = machineChecked

linearizedEinsteinPoissonAuthorityLevel : ProofLevel
linearizedEinsteinPoissonAuthorityLevel = standardImported

schwarzschildBirkhoffRecoveredHere : Set
schwarzschildBirkhoffRecoveredHere = String

schwarzschildBirkhoffBoundary : String
schwarzschildBirkhoffBoundary =
  "This module types the weak-field dimensional and hypothesis chain; it does not prove the repository's Schwarzschild-Birkhoff or non-flat Ricci-convergence obligations."
