module DASHI.Physics.YangMills.BalabanCMP119Section2SourceNativeStateExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
--
-- Tadeusz Bałaban,
-- "Convergent Renormalization Expansions for Lattice Gauge Theories",
-- Communications in Mathematical Physics 119 (1988), 243--285.
-- DOI: 10.1007/BF01217741.
--
-- DIRECT SOURCE LOCATORS
--
-- Sect. 2, especially (2.18)--(2.23), defines the complete effective density
-- and its factorised integration operations.  Equation (2.23) decomposes the
-- effective action into the Wilson term, the fully renormalised regular
-- small-field term E_k, the R-operation term R_k, the boundary term B_k and the
-- vacuum-energy constant.  Equations (2.25)--(2.29) describe E_k and its
-- localized analytic/covariant pieces; (2.30)--(2.33) describe the more
-- strongly decaying R_k pieces; (2.40)--(2.42) describe B_k close to large
-- field regions.  Theorem 1 then preserves this entire inductive class.
--
-- DASHI CONTRIBUTION
--
-- Earlier adapters collapsed CMP119 too early to six rational coordinates.
-- Those coordinates are useful quantitative projections, but they are NOT the
-- source complete density.  This module makes the source object primary:
--
--   rho_k, U_k(V), E_k, R_k, B_k, vacuum energy, coupling and effective action
--
-- all live in one scale-indexed state.  Repository scalar bounds are extracted
-- only by a separate projection.  Thus a proof can no longer satisfy the L5
-- dictionary using six unrelated numbers while silently changing the physical
-- density underneath them.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanYM4RGInvariantRegionPhysicalGapExact as RG

record CMP119ActionAlgebra
    (Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set) : Set₁ where
  field
    assemble :
      ℚ → WilsonTerm → SmallFieldTerm → RTerm → BoundaryTerm → Vacuum → Action
open CMP119ActionAlgebra public

record CMP119Section2SourceNativeState
    (Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set) : Set₁ where
  field
    terminalScale : Nat

    -- Literal scale-k source objects.
    effectiveDensity : Nat → Density
    backgroundField : Nat → Background
    fluctuationFields : Nat → Fluctuation
    runningCoupling : Nat → ℚ

    wilsonActionTerm : Nat → WilsonTerm
    regularSmallFieldTerm : Nat → SmallFieldTerm
    rOperationTerm : Nat → RTerm
    boundaryTerm : Nat → BoundaryTerm
    vacuumEnergy : Nat → Vacuum
    effectiveAction : Nat → Action

    actionAlgebra :
      CMP119ActionAlgebra
        Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum

    -- Literal equation-(2.23) meaning.  The first rational argument is the
    -- source coefficient attached to the Wilson term; the convention mapping
    -- g_k to -1/g_k^2 is deliberately supplied by the physical action algebra,
    -- not hidden as rational division here.
    wilsonCoefficient : Nat → ℚ
    equation223 : ∀ scale →
      effectiveAction scale
      ≡ assemble actionAlgebra
          (wilsonCoefficient scale)
          (wilsonActionTerm scale)
          (regularSmallFieldTerm scale)
          (rOperationTerm scale)
          (boundaryTerm scale)
          (vacuumEnergy scale)

    -- These predicates describe the ACTUAL source objects above.  They are
    -- separated by sector because CMP119 gives different analytic/decay laws:
    -- E is fully renormalised; R has the strong (2.31) exponential estimate;
    -- B is localized near large-field regions and obeys (2.42).
    ELocalizedAnalytic : Nat → SmallFieldTerm → Set
    RLocalizedAnalytic : Nat → RTerm → Set
    BLocalizedAnalytic : Nat → BoundaryTerm → Set
    RegularBackground : Nat → Background → Set
    CompleteDensityForm : Nat → Density → Set

    eSector : ∀ scale → ELocalizedAnalytic scale (regularSmallFieldTerm scale)
    rSector : ∀ scale → RLocalizedAnalytic scale (rOperationTerm scale)
    bSector : ∀ scale → BLocalizedAnalytic scale (boundaryTerm scale)
    regularBackground : ∀ scale →
      RegularBackground scale (backgroundField scale)
    completeDensityForm : ∀ scale →
      CompleteDensityForm scale (effectiveDensity scale)

open CMP119Section2SourceNativeState public

------------------------------------------------------------------------
-- Quantitative repository projection.  All six coordinates MUST be functions
-- of the SAME source-native state/scale.  This is the corrected status of the
-- older six-coordinate carrier: a projection, never the source state itself.
------------------------------------------------------------------------

record CMP119ToYM4ScalarProjection
    {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum : Set}
    (source : CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum) : Set₁ where
  field
    smallFieldNorm : Nat → SmallFieldTerm → ℚ
    largeFieldActivity : Nat → RTerm → BoundaryTerm → ℚ
    conditionalCovarianceNorm : Nat → Background → ℚ
    latticeDecayExponent : Nat → RTerm → BoundaryTerm → ℚ
    inversePhysicalSpacing : Nat → ℚ

open CMP119ToYM4ScalarProjection public

projectYM4State :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {source : CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum} →
  CMP119ToYM4ScalarProjection source → Nat → RG.YM4RGState
projectYM4State {source = source} projection scale =
  RG.rgState
    (runningCoupling source scale)
    (smallFieldNorm projection scale (regularSmallFieldTerm source scale))
    (largeFieldActivity projection scale
      (rOperationTerm source scale) (boundaryTerm source scale))
    (conditionalCovarianceNorm projection scale
      (backgroundField source scale))
    (latticeDecayExponent projection scale
      (rOperationTerm source scale) (boundaryTerm source scale))
    (inversePhysicalSpacing projection scale)

projectedRunningCouplingIsSourceCoupling :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {source : CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (projection : CMP119ToYM4ScalarProjection source) scale →
  RG.runningCoupling (projectYM4State projection scale)
  ≡ runningCoupling source scale
projectedRunningCouplingIsSourceCoupling projection scale =
  Agda.Builtin.Equality.refl

projectedSmallFieldNormComesFromLiteralE :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {source : CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (projection : CMP119ToYM4ScalarProjection source) scale →
  RG.smallFieldPolymerNorm (projectYM4State projection scale)
  ≡ smallFieldNorm projection scale (regularSmallFieldTerm source scale)
projectedSmallFieldNormComesFromLiteralE projection scale =
  Agda.Builtin.Equality.refl

projectedLargeFieldActivityComesFromLiteralRAndB :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {source : CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (projection : CMP119ToYM4ScalarProjection source) scale →
  RG.largeFieldActivity (projectYM4State projection scale)
  ≡ largeFieldActivity projection scale
      (rOperationTerm source scale) (boundaryTerm source scale)
projectedLargeFieldActivityComesFromLiteralRAndB projection scale =
  Agda.Builtin.Equality.refl

projectedCovarianceComesFromLiteralBackground :
  ∀ {Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    {source : CMP119Section2SourceNativeState
      Density Background Fluctuation
      Action WilsonTerm SmallFieldTerm RTerm BoundaryTerm Vacuum}
    (projection : CMP119ToYM4ScalarProjection source) scale →
  RG.conditionalCovarianceNorm (projectYM4State projection scale)
  ≡ conditionalCovarianceNorm projection scale (backgroundField source scale)
projectedCovarianceComesFromLiteralBackground projection scale =
  Agda.Builtin.Equality.refl

cmp119SourceNativeStateLevel : ProofLevel
cmp119SourceNativeStateLevel = machineChecked

cmp119SourceNativeScalarProjectionLevel : ProofLevel
cmp119SourceNativeScalarProjectionLevel = machineChecked

-- Frontier: instantiate the source-native objects from the literal CMP119/122
-- complete-density construction and prove the quantitative norm implications.
-- The six rational coordinates are no longer allowed to stand in for that job.
cmp119LiteralCompleteDensityInstantiationLevel : ProofLevel
cmp119LiteralCompleteDensityInstantiationLevel = conditional

cmp119LiteralSectorNormProjectionBoundsLevel : ProofLevel
cmp119LiteralSectorNormProjectionBoundsLevel = conditional
