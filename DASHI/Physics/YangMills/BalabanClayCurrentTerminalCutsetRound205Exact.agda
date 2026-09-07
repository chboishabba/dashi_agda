{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound205Exact where

------------------------------------------------------------------------
-- ROUND205: FUNCTIONAL OBSERVABLE NORMALIZATION
--
-- For a preferred T5 producer whose observable carrier is literally
-- Configuration -> ℚ, the Path4 gauge-energy observable is defined by
-- composition with the physical Path4 chart.  Its pointwise same-object theorem
-- is refl.  The first representation leaf therefore shrinks from a whole
-- observable realization package to the physical configuration-to-tangent chart.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound204Exact as R204
import DASHI.Physics.YangMills.BalabanClayT5FunctionalPath4GaugeEnergyObservableExact as Functional
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Cylinder
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf205 : Set where
  -- T1.
  physicalConfigurationToPath4TangentChart : T5PreferredContinuumLeaf205
  physicalPath4GaugeEnergyRenormalization : T5PreferredContinuumLeaf205
  physicalPath4GaugeEnergyCompactSublevel : T5PreferredContinuumLeaf205

  -- T2.
  physicalExtractedClusterCylinderAgreement : T5PreferredContinuumLeaf205

  -- T3.
  physicalNormalizationSequentialClosure : T5PreferredContinuumLeaf205
  physicalPositivitySequentialClosure : T5PreferredContinuumLeaf205
  physicalGaugeInvarianceSequentialClosure : T5PreferredContinuumLeaf205

  -- T4 legacy generic closure law.
  physicalGenericGramReflectionSequentialClosure : T5PreferredContinuumLeaf205

  -- T5 split Schwinger semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf205
  physicalContinuumSymmetry : T5PreferredContinuumLeaf205
  physicalContinuumTemperedness : T5PreferredContinuumLeaf205
  physicalContinuumRegularity : T5PreferredContinuumLeaf205
  physicalContinuumClustering : T5PreferredContinuumLeaf205
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf205

preferredT5ContinuumCut205 : List T5PreferredContinuumLeaf205
preferredT5ContinuumCut205 =
  physicalConfigurationToPath4TangentChart ∷
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

functionalPath4GaugeEnergyRealizationCompilerLevel : ProofLevel
functionalPath4GaugeEnergyRealizationCompilerLevel =
  Functional.functionalPath4GaugeEnergyRealizationCompilerLevel

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel =
  Cylinder.cylinderDeterminingClusterUniquenessCompilerLevel

data T1PrerequisiteStatus205 : Set where
  missingPhysicalConfigurationToPath4TangentChart : T1PrerequisiteStatus205
  missingPath4GaugeEnergyRenormalization : T1PrerequisiteStatus205
  missingPath4GaugeEnergyCompactSublevel : T1PrerequisiteStatus205
  readyForSelectedMomentUniformTightnessCompiler : T1PrerequisiteStatus205

preferredCurrentT1Status205 : T1PrerequisiteStatus205
preferredCurrentT1Status205 = missingPhysicalConfigurationToPath4TangentChart

data T2PrerequisiteStatus205 : Set where
  missingExtractedClusterCylinderAgreement : T2PrerequisiteStatus205
  readyForCylinderDeterminingUniquenessCompiler : T2PrerequisiteStatus205

preferredCurrentT2Status205 : T2PrerequisiteStatus205
preferredCurrentT2Status205 = missingExtractedClusterCylinderAgreement

round204CutRetainedForCompatibility : ProofLevel
round204CutRetainedForCompatibility = R204.currentYMTerminalCutsetRound204Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound205Level : ProofLevel
currentYMTerminalCutsetRound205Level = machineChecked

literalPreferredT5ContinuumLeaf205Level : ProofLevel
literalPreferredT5ContinuumLeaf205Level = conditional
