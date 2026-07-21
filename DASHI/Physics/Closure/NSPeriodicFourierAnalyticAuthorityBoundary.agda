module DASHI.Physics.Closure.NSPeriodicFourierAnalyticAuthorityBoundary where

open import Agda.Primitive using (Level; _⊔_; lsuc)

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Source-faithful authority boundary for the periodic Fourier lane.
--
-- Standard Littlewood--Paley, Bernstein, Bony, smooth-multiplier commutator,
-- Sobolev-tail, nonnegative countable summation and BKM/small-data theorems may
-- be imported only through an exact carrier match.  The compact-Gamma profile,
-- inward boundary estimates and all-data chart coverage are not standard
-- consequences of those theorems and stay outside this imported boundary.
------------------------------------------------------------------------

record PublishedPeriodicHarmonicAnalysisAuthority
    {ℓIndex ℓShell ℓTime ℓState ℓBound ℓOrder ℓProp : Level}
    (Index : Set ℓIndex)
    (Shell : Set ℓShell)
    (Time : Set ℓTime)
    (State : Set ℓState)
    (Bound : Set ℓBound)
    (LessEqual : Bound → Bound → Set ℓOrder) :
    Set (lsuc
      (ℓIndex ⊔ ℓShell ⊔ ℓTime ⊔ ℓState ⊔ ℓBound ⊔ ℓOrder ⊔ ℓProp)) where
  field
    Admissible : Index → Time → State → Set ℓProp

    shellVelocityL2 shellGradientL2 shellVorticityLInfinity :
      Shell → State → Bound

    hSobolevNorm highFiveHalvesTail :
      Index → Time → State → Bound

    nearLowHigh nearHighLow nearHighHigh :
      Index → Time → State → Bound

    nearLowHighProduct nearHighLowProduct nearHighHighProduct :
      Index → Time → State → Bound

    farLowCommutator multiplierDifference meanValueMajorant :
      Index → Time → State → Bound

    farHighLeft farHighRight farHighSobolevMajorant :
      Index → Time → State → Bound

    shellCurlEstimate : ∀ shell state →
      LessEqual (shellGradientL2 shell state)
        (shellVelocityL2 shell state)

    shellBernsteinEstimate : ∀ shell state →
      LessEqual (shellVorticityLInfinity shell state)
        (shellGradientL2 shell state)

    bonyLowHighEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (nearLowHigh q τ u) (nearLowHighProduct q τ u)

    bonyHighLowEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (nearHighLow q τ u) (nearHighLowProduct q τ u)

    bonyHighHighEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (nearHighHigh q τ u) (nearHighHighProduct q τ u)

    multiplierMeanValueEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (multiplierDifference q τ u) (meanValueMajorant q τ u)

    farLowCommutatorEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (farLowCommutator q τ u) (multiplierDifference q τ u)

    highSobolevTailEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (highFiveHalvesTail q τ u) (hSobolevNorm q τ u)

    farHighLeftEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (farHighLeft q τ u) (farHighSobolevMajorant q τ u)

    farHighRightEstimate : ∀ q τ u →
      Admissible q τ u →
      LessEqual (farHighRight q τ u) (farHighSobolevMajorant q τ u)

open PublishedPeriodicHarmonicAnalysisAuthority public

record PublishedPeriodicContinuationAuthority
    {i : Level}
    (InitialDatum Solution Time : Set i) : Set (lsuc i) where
  field
    SmoothDivergenceFreeFiniteEnergy : InitialDatum → Set i
    SolvesFrom : InitialDatum → Solution → Set i

    ZeroDatum SmallDatum DiffuseSpectrum : InitialDatum → Set i
    VorticityTimeIntegralFinite : Solution → Time → Set i
    ContinuesBeyond : InitialDatum → Time → Set i

    zeroSolutionGlobal : ∀ u₀ T →
      ZeroDatum u₀ → ContinuesBeyond u₀ T

    smallDataGlobal : ∀ u₀ T →
      SmallDatum u₀ → ContinuesBeyond u₀ T

    bkmContinuation : ∀ u₀ u T →
      SmoothDivergenceFreeFiniteEnergy u₀ →
      SolvesFrom u₀ u →
      VorticityTimeIntegralFinite u T →
      ContinuesBeyond u₀ T

    diffuseSpectrumGivesBKM : ∀ u₀ u T →
      DiffuseSpectrum u₀ →
      SolvesFrom u₀ u →
      VorticityTimeIntegralFinite u T

open PublishedPeriodicContinuationAuthority public

------------------------------------------------------------------------
-- Proof-level audit.
------------------------------------------------------------------------

periodicLittlewoodPaleyBernsteinLevel : ProofLevel
periodicLittlewoodPaleyBernsteinLevel = standardImported

periodicBonyParaproductLevel : ProofLevel
periodicBonyParaproductLevel = standardImported

periodicSmoothMultiplierCommutatorLevel : ProofLevel
periodicSmoothMultiplierCommutatorLevel = standardImported

periodicSobolevHighTailLevel : ProofLevel
periodicSobolevHighTailLevel = standardImported

periodicNonnegativeSummationLevel : ProofLevel
periodicNonnegativeSummationLevel = standardImported

periodicBKMAndSmallDataLevel : ProofLevel
periodicBKMAndSmallDataLevel = standardImported

exactDivergenceCancellationAdapterLevel : ProofLevel
exactDivergenceCancellationAdapterLevel = machineChecked

nearYoungAssemblyLevel : ProofLevel
nearYoungAssemblyLevel = machineChecked

fiveHalvesSummationAssemblyLevel : ProofLevel
fiveHalvesSummationAssemblyLevel = machineChecked

radiusEightTransitivityAssemblyLevel : ProofLevel
radiusEightTransitivityAssemblyLevel = machineChecked

diniFirstExitAssemblyLevel : ProofLevel
diniFirstExitAssemblyLevel = machineChecked

compactGammaPointwiseFiveHalvesProfileLevel : ProofLevel
compactGammaPointwiseFiveHalvesProfileLevel = conjectural

compactGammaBoundaryInwardnessLevel : ProofLevel
compactGammaBoundaryInwardnessLevel = conditional

allOfficialDataCoverageLevel : ProofLevel
allOfficialDataCoverageLevel = conjectural
