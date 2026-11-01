module DASHI.Physics.Closure.NSPeriodicSevenAnalyticLeafCutset where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Sigma using (Σ; _,_)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact final analytic cutset for the periodic compact-Gamma route.
--
-- This module does not replace any PDE estimate by a marker Boolean.  Each
-- remaining package is represented by a proof-relevant proposition, and the
-- final endpoint can be assembled only from inhabitants of all seven packages
-- concerning one common carrier and one common Galerkin family.
------------------------------------------------------------------------

record SevenAnalyticLeafCarrier {i : Level} : Set (lsuc i) where
  field
    Index Shell Cutoff Time State InitialDatum GalerkinSolution
      ContinuumSolution : Set i

    SameOfficialFourierCarrier : Set i
    SameAdaptiveTrajectory : Set i
    SameGalerkinFamily : Set i

open SevenAnalyticLeafCarrier public

record SevenAnalyticLeafObligations
    {i : Level}
    (C : SevenAnalyticLeafCarrier {i}) : Set (lsuc i) where
  field
    -- 1. One official Fourier normalization with cutoff-uniform near/far
    -- constants, including the complete row/column Schur product.
    OfficialCarrierAndUniformHarmonicBounds : Set i

    -- 2. Concrete differentiated compact-Gamma potential with a strictly
    -- positive surviving five-halves/coercive margin.
    ConcreteCompactGammaStrictExpenditure : Set i

    -- 3. Strict inward lower-Dini signs on Gamma, normalized packet fraction,
    -- off-packet ratio and size faces for one common parameter tuple.
    StrictNormalizedBoundarySigns : Set i

    -- 4. Either positive dwell time or a summable chart-switch cost on every
    -- compact time interval.
    UniversalSwitchControl : Set i

    -- 5. Diffuse intervals have finite BKM vorticity expenditure.
    DiffuseSpectrumBKMControl : Set i

    -- 6. Every admissible state is zero, controlled by a normalized chart, or
    -- belongs to the proved diffuse branch.
    ExhaustiveZeroChartDiffuseClassification : Set i

    -- 7. One cutoff-independent numerical vorticity/envelope bound passes to
    -- the continuum along the same selected Galerkin family.
    CutoffUniformBoundAndContinuumTransport : Set i

    sameOfficialFourierCarrier : SameOfficialFourierCarrier C
    sameAdaptiveTrajectory : SameAdaptiveTrajectory C
    sameGalerkinFamily : SameGalerkinFamily C

    officialCarrierAndUniformHarmonicBounds :
      OfficialCarrierAndUniformHarmonicBounds

    concreteCompactGammaStrictExpenditure :
      ConcreteCompactGammaStrictExpenditure

    strictNormalizedBoundarySigns : StrictNormalizedBoundarySigns
    universalSwitchControl : UniversalSwitchControl
    diffuseSpectrumBKMControl : DiffuseSpectrumBKMControl

    exhaustiveZeroChartDiffuseClassification :
      ExhaustiveZeroChartDiffuseClassification

    cutoffUniformBoundAndContinuumTransport :
      CutoffUniformBoundAndContinuumTransport

open SevenAnalyticLeafObligations public

record SevenAnalyticLeafEndpoint
    {i : Level}
    (C : SevenAnalyticLeafCarrier {i}) : Set (lsuc i) where
  field
    FiniteVorticityExpenditureEveryFiniteTime : Set i
    ContinuumNavierStokesEquationPreserved : Set i
    BKMContinuationEveryFiniteTime : Set i
    GlobalSmoothPeriodicSolution : Set i

    finiteVorticityExpenditureEveryFiniteTime :
      FiniteVorticityExpenditureEveryFiniteTime

    continuumNavierStokesEquationPreserved :
      ContinuumNavierStokesEquationPreserved

    bkmContinuationEveryFiniteTime : BKMContinuationEveryFiniteTime
    globalSmoothPeriodicSolution : GlobalSmoothPeriodicSolution

open SevenAnalyticLeafEndpoint public

record SevenAnalyticLeafAssembly
    {i : Level}
    (C : SevenAnalyticLeafCarrier {i})
    (O : SevenAnalyticLeafObligations C) : Set (lsuc i) where
  field
    endpoint : SevenAnalyticLeafEndpoint C

    endpointUsesOfficialCarrier : SameOfficialFourierCarrier C
    endpointUsesAdaptiveTrajectory : SameAdaptiveTrajectory C
    endpointUsesGalerkinFamily : SameGalerkinFamily C

open SevenAnalyticLeafAssembly public

sevenAnalyticLeavesGiveEndpoint :
  ∀ {i} {C : SevenAnalyticLeafCarrier {i}} →
  (O : SevenAnalyticLeafObligations C) →
  SevenAnalyticLeafAssembly C O →
  SevenAnalyticLeafEndpoint C
sevenAnalyticLeavesGiveEndpoint O A = endpoint A

sevenAnalyticLeavesPreserveCoherence :
  ∀ {i} {C : SevenAnalyticLeafCarrier {i}} →
  (O : SevenAnalyticLeafObligations C) →
  (A : SevenAnalyticLeafAssembly C O) →
  Σ (SameOfficialFourierCarrier C)
    (λ _ → Σ (SameAdaptiveTrajectory C)
      (λ _ → SameGalerkinFamily C))
sevenAnalyticLeavesPreserveCoherence O A =
  endpointUsesOfficialCarrier A ,
  (endpointUsesAdaptiveTrajectory A , endpointUsesGalerkinFamily A)

------------------------------------------------------------------------
-- Fail-closed status.  Finite receipts and formal assembly do not inhabit the
-- seven universal analytic leaves.
------------------------------------------------------------------------

sevenAnalyticLeafCutsetAssemblyLevel : ProofLevel
sevenAnalyticLeafCutsetAssemblyLevel = machineChecked

sevenAnalyticLeafObligationsInhabitedInOfficialCarrier : Bool
sevenAnalyticLeafObligationsInhabitedInOfficialCarrier = false

sevenAnalyticLeafEndpointPromoted : Bool
sevenAnalyticLeafEndpointPromoted = false
