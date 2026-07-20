module DASHI.Physics.YangMills.BalabanInfiniteVolumeContinuumLimits where

------------------------------------------------------------------------
-- Infinite-volume and continuum-limit programme (C1--C9).
--
-- The existing BalabanContinuumOSLimit module deliberately keeps the cutoff
-- axioms, convergence witness, and closure of OS0--OS5 separate.  This module
-- refines that abstract seam into the named analytic obligations needed to
-- remove the volume and lattice cutoffs.
--
-- C3 and the final OS closure package are derived.  The uniform estimates,
-- topology, uniqueness, covariance restoration, regularity/growth, and
-- cutoff-uniform clustering remain proof-relevant producer obligations.
------------------------------------------------------------------------

open import Agda.Builtin.Sigma using (Σ)
open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanContinuumOSLimit as OSLimit
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OSGap
import DASHI.Physics.YangMills.CompactLieYangMillsFrontier as Frontier

record InfiniteVolumeContinuumData
    (Cutoff Observable Point Scalar : Set) : Set₁ where
  field
    cutoffSchwinger : Cutoff → Observable → Point → Point → Scalar
    continuumSchwinger : Observable → Point → Point → Scalar

    TestFunctionCollection Bound : Set
    UniformSchwingerBound : TestFunctionCollection → Bound → Set

    -- C1: the bound may depend on n and the selected test functions, but not
    -- on the volume or lattice spacing represented by Cutoff.
    uniformSchwingerBounds :
      (tests : TestFunctionCollection) →
      Σ Bound (λ bound → UniformSchwingerBound tests bound)

    DistributionTopology : Set
    SchwingerFamilyPrecompact : DistributionTopology → Set

    -- C2: tightness/precompactness in the selected distribution topology.
    schwingerFamilyPrecompact :
      (topology : DistributionTopology) →
      SchwingerFamilyPrecompact topology

    SubsequenceLimit : DistributionTopology → Set
    precompactnessYieldsSubsequence :
      (topology : DistributionTopology) →
      SchwingerFamilyPrecompact topology →
      SubsequenceLimit topology

    ContinuumLimitUnique : DistributionTopology → Set

    -- C4: every convergent subsequence has the same continuum Schwinger
    -- system.  Without this field the package produces only a subsequential
    -- theory.
    continuumLimitUnique :
      (topology : DistributionTopology) →
      SubsequenceLimit topology →
      ContinuumLimitUnique topology

    OS0AtCutoff : Cutoff → Set
    OS1AtCutoff : Cutoff → Set
    OS2AtCutoff : Cutoff → Set
    OS3AtCutoff : Cutoff → Set
    OS4AtCutoff : Cutoff → Set
    OS5AtCutoff : Cutoff → Set

    cutoffOS0 : ∀ cutoff → OS0AtCutoff cutoff
    cutoffOS1 : ∀ cutoff → OS1AtCutoff cutoff
    cutoffOS2 : ∀ cutoff → OS2AtCutoff cutoff
    cutoffOS3 : ∀ cutoff → OS3AtCutoff cutoff
    cutoffOS4 : ∀ cutoff → OS4AtCutoff cutoff
    cutoffOS5 : ∀ cutoff → OS5AtCutoff cutoff

    OS0AtLimit : Set
    OS1AtLimit : Set
    OS2AtLimit : Set
    OS3AtLimit : Set
    OS4AtLimit : Set
    OS5AtLimit : Set

    -- C5: lattice covariance restores the full selected Euclidean covariance
    -- group in the limit.
    latticeCovarianceConvergesToEuclideanCovariance : OS1AtLimit

    -- C6: reflection positivity is closed under Schwinger convergence.
    reflectionPositivityClosedUnderSchwingerLimit : OS2AtLimit

    -- C7: permutation symmetry is closed under the same limit.
    schwingerSymmetryClosedUnderLimit : OS3AtLimit

    -- C8: OS0 regularity and OS5 growth are kept as distinct witnesses.
    continuumRegularity : OS0AtLimit
    continuumGrowthBound : OS5AtLimit

    -- C9: the connected-correlation mass parameter is positive and uniform
    -- before the cutoff is removed.  Its concrete exponential inequality is
    -- owned by the application-specific interpretation of OS4AtLimit.
    uniformConnectedCorrelationDecay : OS4AtLimit

open InfiniteVolumeContinuumData public

------------------------------------------------------------------------
-- C3: subsequential convergence follows from C2 and the selected compactness
-- theorem.  This is the first nontrivial implication discharged here.

continuumSubsequenceExists :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) →
  (topology : DistributionTopology dataSet) →
  SubsequenceLimit dataSet topology
continuumSubsequenceExists dataSet topology =
  precompactnessYieldsSubsequence dataSet topology
    (schwingerFamilyPrecompact dataSet topology)

record ConvergesToContinuum
    {Cutoff Observable Point Scalar : Set}
    (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) :
    Set₁ where
  field
    topology : DistributionTopology dataSet
    uniformBounds :
      (tests : TestFunctionCollection dataSet) →
      Σ (Bound dataSet)
        (λ bound → UniformSchwingerBound dataSet tests bound)
    precompact : SchwingerFamilyPrecompact dataSet topology
    subsequence : SubsequenceLimit dataSet topology
    unique : ContinuumLimitUnique dataSet topology

open ConvergesToContinuum public

convergesToContinuumWitness :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) →
  (topology : DistributionTopology dataSet) →
  ConvergesToContinuum dataSet
convergesToContinuumWitness dataSet topology = record
  { topology = topology
  ; uniformBounds = uniformSchwingerBounds dataSet
  ; precompact = schwingerFamilyPrecompact dataSet topology
  ; subsequence = continuumSubsequenceExists dataSet topology
  ; unique = continuumLimitUnique dataSet topology
      (continuumSubsequenceExists dataSet topology)
  }

------------------------------------------------------------------------
-- Adapter into the existing cutoff/convergence/closure architecture.

continuumLimitProblem :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) →
  (topology : DistributionTopology dataSet) →
  OSLimit.SchwingerLimitProblem Cutoff Observable Point Scalar
continuumLimitProblem dataSet topology = record
  { cutoffSchwinger = cutoffSchwinger dataSet
  ; continuumSchwinger = continuumSchwinger dataSet
  ; ConvergesToContinuum = ConvergesToContinuum dataSet
  ; convergesToContinuum = convergesToContinuumWitness dataSet topology
  ; OS0AtCutoff = OS0AtCutoff dataSet
  ; OS1AtCutoff = OS1AtCutoff dataSet
  ; OS2AtCutoff = OS2AtCutoff dataSet
  ; OS3AtCutoff = OS3AtCutoff dataSet
  ; OS4AtCutoff = OS4AtCutoff dataSet
  ; OS5AtCutoff = OS5AtCutoff dataSet
  ; cutoffOS0 = cutoffOS0 dataSet
  ; cutoffOS1 = cutoffOS1 dataSet
  ; cutoffOS2 = cutoffOS2 dataSet
  ; cutoffOS3 = cutoffOS3 dataSet
  ; cutoffOS4 = cutoffOS4 dataSet
  ; cutoffOS5 = cutoffOS5 dataSet
  ; OS0AtLimit = OS0AtLimit dataSet
  ; OS1AtLimit = OS1AtLimit dataSet
  ; OS2AtLimit = OS2AtLimit dataSet
  ; OS3AtLimit = OS3AtLimit dataSet
  ; OS4AtLimit = OS4AtLimit dataSet
  ; OS5AtLimit = OS5AtLimit dataSet
  }

continuumLimitClosure :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) →
  (topology : DistributionTopology dataSet) →
  OSLimit.OSAxiomsClosedUnderLimit (continuumLimitProblem dataSet topology)
continuumLimitClosure dataSet topology = record
  { os0Closed = λ convergence cutoffRegularity → continuumRegularity dataSet
  ; os1Closed = λ convergence cutoffCovariance →
      latticeCovarianceConvergesToEuclideanCovariance dataSet
  ; os2Closed = λ convergence cutoffReflectionPositivity →
      reflectionPositivityClosedUnderSchwingerLimit dataSet
  ; os3Closed = λ convergence cutoffSymmetry →
      schwingerSymmetryClosedUnderLimit dataSet
  ; os4Closed = λ convergence cutoffClustering →
      uniformConnectedCorrelationDecay dataSet
  ; os5Closed = λ convergence cutoffGrowth → continuumGrowthBound dataSet
  }

continuumSchwingerSystem :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) →
  (topology : DistributionTopology dataSet) →
  OSGap.ContinuumSchwingerSystem Observable Point Scalar
continuumSchwingerSystem dataSet topology =
  OSLimit.continuumOSFromLimit
    (continuumLimitProblem dataSet topology)
    (continuumLimitClosure dataSet topology)

continuumOSTarget :
  ∀ {Cutoff Observable Point Scalar : Set} →
  (dataSet : InfiniteVolumeContinuumData Cutoff Observable Point Scalar) →
  (topology : DistributionTopology dataSet) →
  Frontier.ContinuumOSTarget (Observable → Point → Point → Scalar)
continuumOSTarget dataSet topology =
  OSLimit.toContinuumOSTarget
    (continuumLimitProblem dataSet topology)
    (continuumLimitClosure dataSet topology)

continuumLimitBridgeLevel : ProofLevel
continuumLimitBridgeLevel = machineChecked

continuumCompactnessAndUniquenessInputsLevel : ProofLevel
continuumCompactnessAndUniquenessInputsLevel = conjectural

continuumOSClosureAuthorityLevel : ProofLevel
continuumOSClosureAuthorityLevel = standardImported

uniformClusteringInputLevel : ProofLevel
uniformClusteringInputLevel = conjectural
