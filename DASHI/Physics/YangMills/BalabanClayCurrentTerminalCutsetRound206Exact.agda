{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound206Exact where

------------------------------------------------------------------------
-- ROUND206: THREE-CARRIER FIREWALL
--
-- The checked Path4 coercivity theorem lives on rational bond tangents; the
-- physical SU(2) principal logarithm lives on real Lie coordinates; the T5
-- expectation/observable carrier is abstract.  None of those carrier changes is
-- definitionally free.  The preferred cut therefore exposes the exact seams and
-- does not treat a rational Path4 chart as a physical real SU(2) chart.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound205Exact as R205
import DASHI.Physics.YangMills.BalabanPath4SU2RealCoercivityExtensionExact as RealExtension
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact as Path4Markov
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Cylinder
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf206 : Set where
  -- T1 representation / compactness chain.
  physicalPrincipalLogToRealPath4TangentAssembly : T5PreferredContinuumLeaf206
  physicalRealPath4CoercivityExtension : T5PreferredContinuumLeaf206
  physicalRealGaugeEnergyToT5ObservableExpectationSemantics : T5PreferredContinuumLeaf206
  physicalGaugeEnergyRenormalization : T5PreferredContinuumLeaf206
  physicalSelectedExpectationMarkovSemantics : T5PreferredContinuumLeaf206
  physicalGaugeEnergyCompactSublevel : T5PreferredContinuumLeaf206

  -- T2.
  physicalExtractedClusterCylinderAgreement : T5PreferredContinuumLeaf206

  -- T3.
  physicalNormalizationSequentialClosure : T5PreferredContinuumLeaf206
  physicalPositivitySequentialClosure : T5PreferredContinuumLeaf206
  physicalGaugeInvarianceSequentialClosure : T5PreferredContinuumLeaf206

  -- T4 historical generic closure law.
  physicalGenericGramReflectionSequentialClosure : T5PreferredContinuumLeaf206

  -- T5 Schwinger semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf206
  physicalContinuumSymmetry : T5PreferredContinuumLeaf206
  physicalContinuumTemperedness : T5PreferredContinuumLeaf206
  physicalContinuumRegularity : T5PreferredContinuumLeaf206
  physicalContinuumClustering : T5PreferredContinuumLeaf206
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf206

preferredT5ContinuumCut206 : List T5PreferredContinuumLeaf206
preferredT5ContinuumCut206 =
  physicalPrincipalLogToRealPath4TangentAssembly ∷
  physicalRealPath4CoercivityExtension ∷
  physicalRealGaugeEnergyToT5ObservableExpectationSemantics ∷
  physicalGaugeEnergyRenormalization ∷
  physicalSelectedExpectationMarkovSemantics ∷
  physicalGaugeEnergyCompactSublevel ∷
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

realPath4ScalarExtensionCompilerLevel : ProofLevel
realPath4ScalarExtensionCompilerLevel =
  RealExtension.realPath4ScalarExtensionCompilerLevel

realPath4DensityContinuityAuthorityLevel : ProofLevel
realPath4DensityContinuityAuthorityLevel =
  RealExtension.realPath4DensityContinuityAuthorityLevel

physicalSelectedExpectationMarkovSemanticsProducerLevel : ProofLevel
physicalSelectedExpectationMarkovSemanticsProducerLevel =
  Path4Markov.physicalSelectedExpectationMarkovSemanticsLevel

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel =
  Cylinder.cylinderDeterminingClusterUniquenessCompilerLevel

data T1PrerequisiteStatus206 : Set where
  missingPrincipalLogToRealPath4TangentAssembly : T1PrerequisiteStatus206
  missingRealPath4CoercivityExtension : T1PrerequisiteStatus206
  missingRealGaugeEnergyToT5ExpectationSemantics : T1PrerequisiteStatus206
  missingGaugeEnergyRenormalization : T1PrerequisiteStatus206
  missingSelectedExpectationMarkovSemantics : T1PrerequisiteStatus206
  missingGaugeEnergyCompactSublevel : T1PrerequisiteStatus206
  readyForSelectedMomentUniformTightnessCompiler : T1PrerequisiteStatus206

preferredCurrentT1Status206 : T1PrerequisiteStatus206
preferredCurrentT1Status206 = missingPrincipalLogToRealPath4TangentAssembly

data T2PrerequisiteStatus206 : Set where
  missingExtractedClusterCylinderAgreement : T2PrerequisiteStatus206
  readyForCylinderDeterminingUniquenessCompiler : T2PrerequisiteStatus206

preferredCurrentT2Status206 : T2PrerequisiteStatus206
preferredCurrentT2Status206 = missingExtractedClusterCylinderAgreement

round205CutRetainedForCompatibility : ProofLevel
round205CutRetainedForCompatibility = R205.currentYMTerminalCutsetRound205Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound206Level : ProofLevel
currentYMTerminalCutsetRound206Level = machineChecked

literalPreferredT5ContinuumLeaf206Level : ProofLevel
literalPreferredT5ContinuumLeaf206Level = conditional
