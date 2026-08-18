module DASHI.Physics.YangMills.BalabanCMP119Section2CompleteDensityDictionaryExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
-- Section 2, especially equations (2.18)--(2.31), Theorems 1--2 and
-- Corollary 3.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- DASHI CONTRIBUTION
--
-- Correct the source-facing shape of the "complete density" seam.  CMP119
-- Section 2 does NOT introduce five scalar coordinates named K,L,C,mu,a^-1.
-- Its literal inductive object is a complete density represented by the
-- large-field integration/localization operation T_k and the effective action
--
--   A_k = Wilson(g_k,U_k) + E_k + R_k + B_k - E_k^vac,
--
-- with the regular/localized E part, the R-operation part, boundary B part,
-- coupling/small-field scales and analyticity/localization parameters carrying
-- the source bounds.
--
-- This module records that source-native decomposition as one typed object and
-- then makes any lower-dimensional repository summary an explicit DERIVED
-- projection.  In particular, the older DASHI tuple
--
--   (g,K,L,C,mu,aInverse)
--
-- may remain useful downstream, but K,L,C,mu,aInverse must be proved functions
-- of the same Section-2 density data; they are not silently advertised as
-- notation printed by Bałaban.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Literal source-shape carrier for one scale.
------------------------------------------------------------------------

record CMP119Section2CompleteDensity
    (Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay : Set) : Set₁ where
  field
    scale : Nat

    g : Coupling
    rho : Density
    T : Operation
    effectiveAction : Action
    background : Field

    regularE : RegularTerm
    rOperationR : RTerm
    boundaryB : BoundaryTerm
    vacuumE : VacuumTerm

    epsilon : SmallFieldScale
    blockRadius : BlockRadius
    alpha0 alpha1 : AnalyticRadius
    decayKappa : Decay

    -- Equations (2.18), (2.23) and the representation of the density/action are
    -- source equations, represented without committing to an artificial scalar
    -- norm convention here.
    assembleDensity :
      Operation → Action → Density
    assembleAction :
      Coupling → Field → RegularTerm → RTerm → BoundaryTerm → VacuumTerm → Action

    densityEquation :
      rho ≡ assembleDensity T effectiveAction

    actionEquation :
      effectiveAction
      ≡ assembleAction g background regularE rOperationR boundaryB vacuumE

open CMP119Section2CompleteDensity public

------------------------------------------------------------------------
-- Source hypotheses that must survive the RT step.
------------------------------------------------------------------------

record CMP119Section2InductiveBounds
    {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay : Set}
    (dataSet : CMP119Section2CompleteDensity
      Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay) : Set₁ where
  field
    EffectiveCouplingInSmallInterval : Set
    effectiveCouplingInSmallInterval : EffectiveCouplingInSmallInterval

    RegularLocalizedAnalyticBound : Set
    regularLocalizedAnalyticBound : RegularLocalizedAnalyticBound

    ROperationLocalizedDecayBound : Set
    rOperationLocalizedDecayBound : ROperationLocalizedDecayBound

    BoundaryLocalizedDecayBound : Set
    boundaryLocalizedDecayBound : BoundaryLocalizedDecayBound

    EuclideanCovariance : Set
    euclideanCovariance : EuclideanCovariance

    GaugeCovariance : Set
    gaugeCovariance : GaugeCovariance

open CMP119Section2InductiveBounds public

------------------------------------------------------------------------
-- Any compact DASHI state is explicitly a projection of the same density.
------------------------------------------------------------------------

record CompleteDensityDerivedSummary
    {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay : Set}
    (dataSet : CMP119Section2CompleteDensity
      Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay)
    (Bound : Set) : Set₁ where
  field
    smallFieldPolymerNorm :
      CMP119Section2CompleteDensity.RegularTerm dataSet → Bound
    largeFieldActivityNorm :
      CMP119Section2CompleteDensity.RTerm dataSet →
      CMP119Section2CompleteDensity.BoundaryTerm dataSet → Bound
    conditionalCovarianceNorm :
      CMP119Section2CompleteDensity.Operation dataSet → Bound
    localizationExponent :
      CMP119Section2CompleteDensity.Decay dataSet → Bound
    inverseLatticeSpacing : Nat → Bound

open CompleteDensityDerivedSummary public

record DASHICompleteDensitySummary (Coupling Bound : Set) : Set where
  constructor dashiDensitySummary
  field
    gSummary : Coupling
    KSummary LSummary CSummary muSummary aInverseSummary : Bound
open DASHICompleteDensitySummary public

summaryFromCMP119Section2 :
  ∀ {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay Bound}
    (dataSet : CMP119Section2CompleteDensity
      Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay) →
    CompleteDensityDerivedSummary dataSet Bound →
    DASHICompleteDensitySummary Coupling Bound
summaryFromCMP119Section2 dataSet meaning =
  dashiDensitySummary
    (g dataSet)
    (smallFieldPolymerNorm meaning (regularE dataSet))
    (largeFieldActivityNorm meaning (rOperationR dataSet) (boundaryB dataSet))
    (conditionalCovarianceNorm meaning (T dataSet))
    (localizationExponent meaning (decayKappa dataSet))
    (inverseLatticeSpacing meaning (scale dataSet))

summaryCouplingIsSourceCoupling :
  ∀ {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay Bound}
    (dataSet : CMP119Section2CompleteDensity
      Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay)
    (meaning : CompleteDensityDerivedSummary dataSet Bound) →
  gSummary (summaryFromCMP119Section2 dataSet meaning) ≡ g dataSet
summaryCouplingIsSourceCoupling dataSet meaning = refl

summaryKIsRegularPartProjection :
  ∀ {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay Bound}
    (dataSet : CMP119Section2CompleteDensity
      Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay)
    (meaning : CompleteDensityDerivedSummary dataSet Bound) →
  KSummary (summaryFromCMP119Section2 dataSet meaning)
  ≡ smallFieldPolymerNorm meaning (regularE dataSet)
summaryKIsRegularPartProjection dataSet meaning = refl

summaryLIsLargeFieldProjection :
  ∀ {Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay Bound}
    (dataSet : CMP119Section2CompleteDensity
      Coupling Density Operation Action Field
      RegularTerm RTerm BoundaryTerm VacuumTerm
      SmallFieldScale BlockRadius AnalyticRadius Decay)
    (meaning : CompleteDensityDerivedSummary dataSet Bound) →
  LSummary (summaryFromCMP119Section2 dataSet meaning)
  ≡ largeFieldActivityNorm meaning (rOperationR dataSet) (boundaryB dataSet)
summaryLIsLargeFieldProjection dataSet meaning = refl

cmp119Section2CompleteDensitySourceShapeLevel : ProofLevel
cmp119Section2CompleteDensitySourceShapeLevel = machineChecked

cmp119Section2DerivedSummarySameObjectLevel : ProofLevel
cmp119Section2DerivedSummarySameObjectLevel = machineChecked

-- Remaining literal source-to-DASHI dictionary: instantiate the five projection
-- functionals by the precise CMP119/CMP122 localization/norm conventions and
-- prove the bounds required by the downstream YM4 region.  The key correction
-- is that those five projections are now visibly DERIVED from E/R/B/T/scale,
-- rather than falsely presented as five names printed in Section 2.
cmp119Section2PhysicalProjectionBoundsLevel : ProofLevel
cmp119Section2PhysicalProjectionBoundsLevel = conditional
