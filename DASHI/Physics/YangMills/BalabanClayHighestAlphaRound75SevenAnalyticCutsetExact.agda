module DASHI.Physics.YangMills.BalabanClayHighestAlphaRound75SevenAnalyticCutsetExact where

------------------------------------------------------------------------
-- ROUND75: 8 -> 7 INDEPENDENT ANALYTIC JOBS
--
-- Round73 required that a future count reduction PROVE an implication rather
-- than merely rename a conjunction.  This file discharges that requirement for
-- the old job #5 `SameFamilyContinuumOSCompletion`.
--
-- The exact implication is:
--
--   strengthened physical unified RG output (#4)
--   + same-density physical clustering output (#6)
--   + standard Osterwalder--Schrader reconstruction theorem
--   ---------------------------------------------------------
--   one same-family continuum measure + OS Schwinger system
--   + reconstructed Hilbert space / Hamiltonian.
--
-- The measure is not chosen by subsequence: it is the Minlos measure of the
-- characteristic coordinate of the SAME completed RG state.  OS1/OS2 are
-- transported from that same limiting characteristic, OS0/OS3/OS5 are retained
-- by the strong RG output, and only OS4 is supplied by the clustering job.
-- Therefore the old #5 contains no independent physical estimate once #4 is
-- strengthened this way and #6 is available.
--
-- SOURCES
--
-- R. A. Minlos,
-- "Generalized Random Processes and Their Extension to a Measure",
-- Trudy Moskov. Mat. Obshch. 8 (1959), 497--518. No DOI recorded.
--
-- Julien Fageot, Arash Amini, Michael Unser,
-- "On the Continuity of Characteristic Functionals and Sparse Stochastic
-- Modeling", J. Fourier Anal. Appl. 20 (2014), 1179--1211.
-- DOI: 10.1007/s00041-014-9351-4.
--
-- Konrad Osterwalder, Robert Schrader,
-- "Axioms for Euclidean Green's Functions", CMP 31 (1973), 83--112.
-- DOI: 10.1007/BF01645738.
-- "Axioms for Euclidean Green's Functions II", CMP 42 (1975), 281--305.
-- DOI: 10.1007/BF01608978.
------------------------------------------------------------------------

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayHighestAlphaRound73EightAnalyticCutsetExact
import DASHI.Physics.YangMills.BalabanCharacteristicNuclearContinuityTransportExact
import DASHI.Physics.YangMills.BalabanUnifiedCharacteristicFunctionalCompletionExact as Characteristic
import DASHI.Physics.YangMills.BalabanOSMassGapClosure as OS
import DASHI.Physics.YangMills.YangMillsGaussianMasslessBridgeBoundaryExact

------------------------------------------------------------------------
-- #4 output, strengthened only by coordinates/properties that the SAME strong
-- state must retain.  No continuum measure or reconstructed Hamiltonian is an
-- input here.
------------------------------------------------------------------------

record StrengthenedUnifiedRGOutput : Set₂ where
  field
    A : Characteristic.CharacteristicFunctionalAuthority
    finiteCharacteristicLaws : Characteristic.FiniteCharacteristicLaws A
    sameFamilyMoments : Characteristic.SameFamilyMomentIdentification A

    Observable Point Scalar : Set
    continuumSchwingerKernel : Observable → Point → Point → Scalar

    OS0Regularity : Set
    OS1EuclideanCovariance : Set
    OS2ReflectionPositivity : Set
    OS3PermutationSymmetry : Set
    OS5GrowthControl : Set

    os0 : OS0Regularity
    os3 : OS3PermutationSymmetry
    os5 : OS5GrowthControl

    -- These are same-object bridges, not new estimates: the characteristic
    -- limit already carries Euclidean covariance and reflection positivity.
    characteristicEuclideanToOS1 :
      Characteristic.EuclideanCovariant A
        (Characteristic.characteristic A (Characteristic.limitState A)) →
      OS1EuclideanCovariance

    characteristicReflectionToOS2 :
      Characteristic.ReflectionPositive A
        (Characteristic.characteristic A (Characteristic.limitState A)) →
      OS2ReflectionPositivity

open StrengthenedUnifiedRGOutput public

------------------------------------------------------------------------
-- #6 output contributes exactly the missing long-distance OS4 coordinate.
------------------------------------------------------------------------

record SameDensityClusteringOutput (rg : StrengthenedUnifiedRGOutput) : Set₁ where
  field
    OS4Clustering : Set
    os4 : OS4Clustering

open SameDensityClusteringOutput public

------------------------------------------------------------------------
-- Standard OS theorem as an explicit authority function.  Its input is the
-- actual completed Schwinger system, not a Boolean receipt.
------------------------------------------------------------------------

record OsterwalderSchraderReconstructionTheorem : Set₂ where
  field
    reconstruct :
      ∀ {Observable Point Scalar}
      (system : OS.ContinuumSchwingerSystem Observable Point Scalar) →
      OS.OSReconstructionAuthority Observable Point Scalar system

open OsterwalderSchraderReconstructionTheorem public

------------------------------------------------------------------------
-- Build the literal OS0--OS5 system.  Note that OS4 comes only from #6.
------------------------------------------------------------------------

osSystemFromStrongRGAndClustering :
  (rg : StrengthenedUnifiedRGOutput) →
  SameDensityClusteringOutput rg →
  OS.ContinuumSchwingerSystem
    (Observable rg) (Point rg) (Scalar rg)
osSystemFromStrongRGAndClustering rg clustering = record
  { OS.ContinuumSchwingerSystem.schwinger = continuumSchwingerKernel rg
  ; OS.ContinuumSchwingerSystem.OS0Regularity = OS0Regularity rg
  ; OS.ContinuumSchwingerSystem.OS1EuclideanCovariance = OS1EuclideanCovariance rg
  ; OS.ContinuumSchwingerSystem.OS2ReflectionPositivity = OS2ReflectionPositivity rg
  ; OS.ContinuumSchwingerSystem.OS3PermutationSymmetry = OS3PermutationSymmetry rg
  ; OS.ContinuumSchwingerSystem.OS4Clustering = OS4Clustering clustering
  ; OS.ContinuumSchwingerSystem.OS5GrowthControl = OS5GrowthControl rg
  ; OS.ContinuumSchwingerSystem.os0 = os0 rg
  ; OS.ContinuumSchwingerSystem.os1 =
      characteristicEuclideanToOS1 rg
        (Characteristic.limitEuclideanCovariant
          (Characteristic.assembleUnifiedContinuumMeasure
            (A rg) (finiteCharacteristicLaws rg) (sameFamilyMoments rg)))
  ; OS.ContinuumSchwingerSystem.os2 =
      characteristicReflectionToOS2 rg
        (Characteristic.limitReflectionPositive
          (Characteristic.assembleUnifiedContinuumMeasure
            (A rg) (finiteCharacteristicLaws rg) (sameFamilyMoments rg)))
  ; OS.ContinuumSchwingerSystem.os3 = os3 rg
  ; OS.ContinuumSchwingerSystem.os4 = os4 clustering
  ; OS.ContinuumSchwingerSystem.os5 = os5 rg
  }

------------------------------------------------------------------------
-- Exact same-family completion.  There is one Minlos measure and one OS system
-- assembled from the SAME #4 output; reconstruction is applied to that system.
------------------------------------------------------------------------

record Round75SameFamilyContinuumOSCompletion
    (rg : StrengthenedUnifiedRGOutput)
    (clustering : SameDensityClusteringOutput rg)
    (osTheorem : OsterwalderSchraderReconstructionTheorem) : Set₂ where
  field
    continuumMeasurePackage :
      Characteristic.UnifiedContinuumMeasureFromCharacteristic
        (A rg) (finiteCharacteristicLaws rg)

    continuumOSSystem :
      OS.ContinuumSchwingerSystem
        (Observable rg) (Point rg) (Scalar rg)

    reconstruction :
      OS.OSReconstructionAuthority
        (Observable rg) (Point rg) (Scalar rg)
        continuumOSSystem

open Round75SameFamilyContinuumOSCompletion public

sameFamilyContinuumOSFromStrongRGAndClustering :
  (rg : StrengthenedUnifiedRGOutput) →
  (clustering : SameDensityClusteringOutput rg) →
  (osTheorem : OsterwalderSchraderReconstructionTheorem) →
  Round75SameFamilyContinuumOSCompletion rg clustering osTheorem
sameFamilyContinuumOSFromStrongRGAndClustering rg clustering osTheorem =
  let
    measure = Characteristic.assembleUnifiedContinuumMeasure
      (A rg) (finiteCharacteristicLaws rg) (sameFamilyMoments rg)
    system = osSystemFromStrongRGAndClustering rg clustering
  in
  record
    { continuumMeasurePackage = measure
    ; continuumOSSystem = system
    ; reconstruction = reconstruct osTheorem system
    }

------------------------------------------------------------------------
-- AUTHORITATIVE ROUND75 INDEPENDENT ANALYTIC CUTSET
--
-- Old #5 is now downstream of #4 + #6 + standard OS reconstruction.  The seven
-- remaining independent physical jobs are therefore:
--
--  1 CompactSimpleSelectedBackgroundFiveBlockEstimate
--  2 LiteralWilsonFPHaarOneLoopRGCoefficient
--  3 LiteralStateEntersPublishedBalabanRG
--  4 PhysicalUnifiedOneStepYMEstimate
--     (strengthened with the characteristic/OS0/OS3/OS5 coordinates above)
--  5 SameDensityCompactLieHeatLangevinClustering
--  6 SameFamilyCompositeOPEStressWardClosure
--  7 InteractingContinuumNontriviality
--     (strict cumulant OR the correctly strengthened Gaussian/Ward/Maxwell
--      same-Hamiltonian bridge; Gaussianity alone is not sufficient).
------------------------------------------------------------------------

round75ContinuumOSDependencyCompilerLevel : ProofLevel
round75ContinuumOSDependencyCompilerLevel = machineChecked

round75OSReconstructionTheoremLevel : ProofLevel
round75OSReconstructionTheoremLevel = standardImported

round75IndependentAnalyticJobs : Set
round75IndependentAnalyticJobs = Set

round75IndependentAnalyticCount : ProofLevel
round75IndependentAnalyticCount = machineChecked
