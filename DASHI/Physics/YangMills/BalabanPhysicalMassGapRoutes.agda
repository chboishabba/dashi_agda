module DASHI.Physics.YangMills.BalabanPhysicalMassGapRoutes where

------------------------------------------------------------------------
-- Two explicit routes to the physical Yang--Mills mass gap.
--
-- Route 1 records exponential decay of connected Euclidean-time
-- correlations and imports the standard spectral transfer theorem.
-- Route 2 names the finite-cutoff separation, uniform positive lower bound,
-- strong-resolvent convergence, and limit-survival components consumed by
-- the existing mass-gap assembly bridge.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.BalabanMassGapSurvival as Survival

------------------------------------------------------------------------
-- Route 1: exponential time clustering implies a spectral gap.

record ExponentialTimeClusteringData
    (Observable Time Scalar Bound Hamiltonian : Set) : Set₁ where
  field
    vacuum : Observable
    connectedCorrelation : Observable → Observable → Time → Scalar

    massParameter : Bound
    correlationConstant : Observable → Observable → Bound
    Positive : Bound → Set
    positiveMassParameter : Positive massParameter

    ExponentialDecayBound :
      Observable → Observable → Time → Bound → Bound → Set

    exponentialTimeClustering :
      ∀ A B t →
      ExponentialDecayBound A B t
        (correlationConstant A B)
        massParameter

    reconstructedHamiltonian : Hamiltonian

open ExponentialTimeClusteringData public

-- M1: the connected correlation obeys the selected exponential bound.
exponentialTimeClusteringBound :
  ∀ {Observable Time Scalar Bound Hamiltonian : Set} →
  (dataSet :
    ExponentialTimeClusteringData
      Observable Time Scalar Bound Hamiltonian) →
  ∀ A B t →
  ExponentialDecayBound dataSet A B t
    (correlationConstant dataSet A B)
    (massParameter dataSet)
exponentialTimeClusteringBound dataSet =
  exponentialTimeClustering dataSet

record ExponentialClusteringSpectrumAuthority
    {Observable Time Scalar Bound Hamiltonian : Set}
    (dataSet :
      ExponentialTimeClusteringData
        Observable Time Scalar Bound Hamiltonian) : Set₁ where
  field
    SpectrumSeparatedBy : Hamiltonian → Bound → Set
    exponentialClusteringTransfer :
      (∀ A B t →
        ExponentialDecayBound dataSet A B t
          (correlationConstant dataSet A B)
          (massParameter dataSet)) →
      SpectrumSeparatedBy
        (reconstructedHamiltonian dataSet)
        (massParameter dataSet)

open ExponentialClusteringSpectrumAuthority public

-- M2: the standard clustering-to-spectrum theorem, packaged as the physical
-- certificate spec(H) subset {0} union [m_G,infinity).
exponentialTimeClusteringImpliesSpectrumGap :
  ∀ {Observable Time Scalar Bound Hamiltonian : Set} →
  (dataSet :
    ExponentialTimeClusteringData
      Observable Time Scalar Bound Hamiltonian) →
  ExponentialClusteringSpectrumAuthority dataSet →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
exponentialTimeClusteringImpliesSpectrumGap dataSet authority = record
  { hamiltonian = reconstructedHamiltonian dataSet
  ; gap = massParameter dataSet
  ; Positive = Positive dataSet
  ; gapPositive = positiveMassParameter dataSet
  ; SpectrumAboveVacuumGap =
      SpectrumSeparatedBy authority
        (reconstructedHamiltonian dataSet)
        (massParameter dataSet)
  ; spectrumAboveVacuumGap =
      exponentialClusteringTransfer authority
        (exponentialTimeClusteringBound dataSet)
  }

------------------------------------------------------------------------
-- Route 2: uniform finite-cutoff gaps survive strong-resolvent convergence.

-- M3: every cutoff Hamiltonian has its stated finite-cutoff spectral gap.
finiteCutoffGaps :
  ∀ {Cutoff Hamiltonian Bound : Set} →
  (dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound) →
  ∀ cutoff →
  Survival.SpectrumSeparatedBy dataSet
    (Survival.cutoffHamiltonian dataSet cutoff)
    (Survival.cutoffGap dataSet cutoff)
finiteCutoffGaps dataSet = Survival.cutoffSpectrumSeparated dataSet

-- M4: one strictly positive lower bound works for every cutoff.
uniformPositiveCutoffGap :
  ∀ {Cutoff Hamiltonian Bound : Set} →
  (dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound) →
  ∀ cutoff →
  Survival.LessEqual dataSet
    (Survival.lowerGap dataSet)
    (Survival.cutoffGap dataSet cutoff)
uniformPositiveCutoffGap dataSet = Survival.lowerBoundUniform dataSet

record StrongResolventConvergenceData
    {Cutoff Hamiltonian Bound : Set}
    (dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound) : Set₁ where
  field
    continuumHamiltonian : Hamiltonian
    StrongResolventConvergesTo :
      (Cutoff → Hamiltonian) → Hamiltonian → Set
    strongResolventConvergence :
      StrongResolventConvergesTo
        (Survival.cutoffHamiltonian dataSet)
        continuumHamiltonian

open StrongResolventConvergenceData public

-- M5: the cutoff Hamiltonians converge in the selected strong-resolvent
-- topology.
cutoffHamiltoniansConvergeStrongResolvent :
  ∀ {Cutoff Hamiltonian Bound : Set}
    {dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound} →
  (convergence : StrongResolventConvergenceData dataSet) →
  StrongResolventConvergesTo convergence
    (Survival.cutoffHamiltonian dataSet)
    (continuumHamiltonian convergence)
cutoffHamiltoniansConvergeStrongResolvent convergence =
  strongResolventConvergence convergence

record StrongResolventGapSurvivalAuthority
    {Cutoff Hamiltonian Bound : Set}
    (dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound)
    (convergence : StrongResolventConvergenceData dataSet) : Set₁ where
  field
    strongResolventGapTransfer :
      StrongResolventConvergesTo convergence
        (Survival.cutoffHamiltonian dataSet)
        (continuumHamiltonian convergence) →
      (∀ cutoff →
        Survival.LessEqual dataSet
          (Survival.lowerGap dataSet)
          (Survival.cutoffGap dataSet cutoff)) →
      (∀ cutoff →
        Survival.SpectrumSeparatedBy dataSet
          (Survival.cutoffHamiltonian dataSet cutoff)
          (Survival.cutoffGap dataSet cutoff)) →
      Survival.SpectrumSeparatedBy dataSet
        (continuumHamiltonian convergence)
        (Survival.lowerGap dataSet)

open StrongResolventGapSurvivalAuthority public

strongResolventSurvivalAuthority :
  ∀ {Cutoff Hamiltonian Bound : Set}
    {dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound} →
  (convergence : StrongResolventConvergenceData dataSet) →
  StrongResolventGapSurvivalAuthority dataSet convergence →
  Survival.GapSurvivesContinuumAuthority dataSet
strongResolventSurvivalAuthority convergence authority = record
  { continuumHamiltonian = continuumHamiltonian convergence
  ; uniformGapTransfer = λ lowerBounds cutoffGaps →
      strongResolventGapTransfer authority
        (cutoffHamiltoniansConvergeStrongResolvent convergence)
        lowerBounds
        cutoffGaps
  }

-- M6: no spectrum can collapse into the interval (0,m*) in the limit.
gapSurvivesTheLimit :
  ∀ {Cutoff Hamiltonian Bound : Set} →
  (dataSet : Survival.UniformCutoffGapData Cutoff Hamiltonian Bound) →
  (convergence : StrongResolventConvergenceData dataSet) →
  StrongResolventGapSurvivalAuthority dataSet convergence →
  OSGap.PhysicalMassGapCertificate Hamiltonian Bound
gapSurvivesTheLimit dataSet convergence authority =
  Survival.survivingPhysicalMassGap dataSet
    (strongResolventSurvivalAuthority convergence authority)

------------------------------------------------------------------------
-- Proof-level ledger.

exponentialTimeClusteringInputLevel : ProofLevel
exponentialTimeClusteringInputLevel = conjectural

exponentialClusteringSpectrumTransferLevel : ProofLevel
exponentialClusteringSpectrumTransferLevel = standardImported

finiteCutoffGapInputLevel : ProofLevel
finiteCutoffGapInputLevel = conjectural

uniformPositiveCutoffGapLevel : ProofLevel
uniformPositiveCutoffGapLevel = conjectural

strongResolventConvergenceInputLevel : ProofLevel
strongResolventConvergenceInputLevel = conjectural

strongResolventGapSurvivalLevel : ProofLevel
strongResolventGapSurvivalLevel = standardImported

physicalMassGapRouteAssemblyLevel : ProofLevel
physicalMassGapRouteAssemblyLevel = machineChecked
