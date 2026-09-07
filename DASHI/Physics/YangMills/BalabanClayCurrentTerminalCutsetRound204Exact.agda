{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound204Exact where

------------------------------------------------------------------------
-- ROUND204: CONSOLIDATED LEAST-PRIVILEGE T5 FRONTIER
--
-- T1 uses the literal Path4 gauge energy realization.  T2 no longer asks for
-- primitive measure equality: cylinder agreement plus a determining class
-- produces cluster uniqueness.  T3 and T5 are split into their actual semantic
-- coordinates rather than retained as broad bundled labels.  T4 keeps only the
-- generic reflection-positive closure law demanded by the historical
-- FiniteToContinuumOSClosure carrier; selected-target reflection positivity is
-- already produced by the quantitative complete-Gram route.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound203Exact as R203
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5PhysicalMeasureGramContinuityExact as Gram
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf204 : Set where
  -- T1: compactness/tightness representation seam.
  physicalPath4GaugeEnergyObservableRealization : T5PreferredContinuumLeaf204
  physicalPath4GaugeEnergyRenormalization : T5PreferredContinuumLeaf204
  physicalPath4GaugeEnergyCompactSublevel : T5PreferredContinuumLeaf204

  -- T2: equality is compiler output from a determining class.
  physicalExtractedClusterCylinderAgreement : T5PreferredContinuumLeaf204

  -- T3: split measure-property closure.
  physicalNormalizationSequentialClosure : T5PreferredContinuumLeaf204
  physicalPositivitySequentialClosure : T5PreferredContinuumLeaf204
  physicalGaugeInvarianceSequentialClosure : T5PreferredContinuumLeaf204

  -- T4: only the generic legacy closure law remains; selected continuum RP is
  -- already produced directly by PhysicalMeasureToOSGramData.
  physicalGenericGramReflectionSequentialClosure : T5PreferredContinuumLeaf204

  -- T5: split continuum Schwinger semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf204
  physicalContinuumSymmetry : T5PreferredContinuumLeaf204
  physicalContinuumTemperedness : T5PreferredContinuumLeaf204
  physicalContinuumRegularity : T5PreferredContinuumLeaf204
  physicalContinuumClustering : T5PreferredContinuumLeaf204
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf204

preferredT5ContinuumCut204 : List T5PreferredContinuumLeaf204
preferredT5ContinuumCut204 =
  physicalPath4GaugeEnergyObservableRealization ∷
  physicalPath4GaugeEnergyRenormalization ∷
  physicalPath4GaugeEnergyCompactSublevel ∷
  physicalExtractedClusterCylinderAgreement ∷
  physicalNormalizationSequentialClosure ∷
  physicalPositivitySequentialClosure ∷
  physicalGaugeInvarianceSequentialClosure ∷
  physicalGenericGramReflectionSequentialClosure ∷
  physicalContinuumEuclideanCovariance ∷
  physicalContinuumSymmetry ∷
  physicalContinuumTemperedness ∷
  physicalContinuumRegularity ∷
  physicalContinuumClustering ∷
  physicalGramReflectionToSchwingerReflectionMeaning ∷ []

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel =
  Cylinder.cylinderDeterminingClusterUniquenessCompilerLevel

cylinderDeterminingAuthorityLevel : ProofLevel
cylinderDeterminingAuthorityLevel = Cylinder.cylinderDeterminingAuthorityLevel

-- The selected continuum measure already has complete-Gram reflection
-- positivity from the mature quantitative OS-Gram package.  It is not a fresh
-- physical leaf in this scheduler.
selectedContinuumGramReflectionPositiveProducerLevel : ProofLevel
selectedContinuumGramReflectionPositiveProducerLevel =
  Gram.physicalMeasureToOSGramAdapterLevel

data T1PrerequisiteStatus204 : Set where
  missingPath4GaugeEnergyObservableRealization : T1PrerequisiteStatus204
  missingPath4GaugeEnergyRenormalization : T1PrerequisiteStatus204
  missingPath4GaugeEnergyCompactSublevel : T1PrerequisiteStatus204
  readyForSelectedMomentUniformTightnessCompiler : T1PrerequisiteStatus204

preferredCurrentT1Status204 : T1PrerequisiteStatus204
preferredCurrentT1Status204 = missingPath4GaugeEnergyObservableRealization

data T2PrerequisiteStatus204 : Set where
  missingExtractedClusterCylinderAgreement : T2PrerequisiteStatus204
  readyForCylinderDeterminingUniquenessCompiler : T2PrerequisiteStatus204

preferredCurrentT2Status204 : T2PrerequisiteStatus204
preferredCurrentT2Status204 = missingExtractedClusterCylinderAgreement

round203CutRetainedForCompatibility : ProofLevel
round203CutRetainedForCompatibility = R203.currentYMTerminalCutsetRound203Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound204Level : ProofLevel
currentYMTerminalCutsetRound204Level = machineChecked

literalPreferredT5ContinuumLeaf204Level : ProofLevel
literalPreferredT5ContinuumLeaf204Level = conditional
