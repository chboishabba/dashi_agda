{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound207Exact where

------------------------------------------------------------------------
-- ROUND207: GLOBAL-TIGHTNESS CORRECTION / GENUINE T1 WALL
--
-- The configured Path4 Hessian coercivity theorem is local to the small-field
-- tangent chart.  The selected T5 measure is not typed as supported entirely in
-- that chart.  Therefore the Path4 route is retained as an optional producer
-- experiment, not accepted as payment for global compact containment without an
-- additional globalization/support theorem.
--
-- The least-privilege preferred T1 requirement is consequently the exact global
-- theorem consumed by the already-built moment->tightness compiler: the typed
-- selected moment bound controls escape from one admissible compact witness.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound206Exact as R206
import DASHI.Physics.YangMills.BalabanClayT5MomentCompactContainmentExact as Moment
import DASHI.Physics.YangMills.BalabanClayT5CylinderDeterminingClusterUniquenessExact as Cylinder
import DASHI.Physics.YangMills.BalabanClayT5Path4GaugeEnergyMarkovBridgeExact as Path4
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf207 : Set where
  -- T1: exact global selected-measure theorem. The existing typed moment bound
  -- itself is compiler input and is not a new physical leaf.
  physicalGlobalMomentCompactContainment : T5PreferredContinuumLeaf207

  -- T2: cluster equality is derived from these cylinder expectations plus a
  -- determining-class authority.
  physicalExtractedClusterCylinderAgreement : T5PreferredContinuumLeaf207

  -- T3.
  physicalNormalizationSequentialClosure : T5PreferredContinuumLeaf207
  physicalPositivitySequentialClosure : T5PreferredContinuumLeaf207
  physicalGaugeInvarianceSequentialClosure : T5PreferredContinuumLeaf207

  -- T4: generic closure demanded by the historical broad closure carrier.
  physicalGenericGramReflectionSequentialClosure : T5PreferredContinuumLeaf207

  -- T5: split Schwinger semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf207
  physicalContinuumSymmetry : T5PreferredContinuumLeaf207
  physicalContinuumTemperedness : T5PreferredContinuumLeaf207
  physicalContinuumRegularity : T5PreferredContinuumLeaf207
  physicalContinuumClustering : T5PreferredContinuumLeaf207
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf207

preferredT5ContinuumCut207 : List T5PreferredContinuumLeaf207
preferredT5ContinuumCut207 =
  physicalGlobalMomentCompactContainment ∷
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

-- Existing cutoff-uniform typed moment theorem + one global containment theorem
-- is enough to compile selected-sequence uniform tightness.
typedMomentToUniformTightnessCompilerLevel : ProofLevel
typedMomentToUniformTightnessCompilerLevel =
  Moment.typedMomentToUniformTightnessCompilerLevel

physicalGlobalMomentCompactContainmentProducerLevel : ProofLevel
physicalGlobalMomentCompactContainmentProducerLevel =
  Moment.physicalMomentCompactContainmentLevel

cylinderDeterminingClusterUniquenessCompilerLevel : ProofLevel
cylinderDeterminingClusterUniquenessCompilerLevel =
  Cylinder.cylinderDeterminingClusterUniquenessCompilerLevel

-- The Path4 route remains useful as a local candidate producer, but its selected
-- expectation/Markov semantics is still explicitly conditional and no theorem
-- here promotes it to the global selected-measure containment statement.
path4LocalCandidateCompilerLevel : ProofLevel
path4LocalCandidateCompilerLevel = Path4.path4SelectedMomentContainmentCompilerLevel

path4SelectedExpectationSemanticsStillConditional : ProofLevel
path4SelectedExpectationSemanticsStillConditional =
  Path4.physicalSelectedExpectationMarkovSemanticsLevel

data T1PrerequisiteStatus207 : Set where
  missingGlobalMomentCompactContainment : T1PrerequisiteStatus207
  readyForGlobalUniformTightnessCompiler : T1PrerequisiteStatus207

preferredCurrentT1Status207 : T1PrerequisiteStatus207
preferredCurrentT1Status207 = missingGlobalMomentCompactContainment

data T2PrerequisiteStatus207 : Set where
  missingExtractedClusterCylinderAgreement : T2PrerequisiteStatus207
  readyForCylinderDeterminingUniquenessCompiler : T2PrerequisiteStatus207

preferredCurrentT2Status207 : T2PrerequisiteStatus207
preferredCurrentT2Status207 = missingExtractedClusterCylinderAgreement

round206Path4RouteRetainedAsOptionalProducer : ProofLevel
round206Path4RouteRetainedAsOptionalProducer = R206.currentYMTerminalCutsetRound206Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound207Level : ProofLevel
currentYMTerminalCutsetRound207Level = machineChecked

literalPreferredT5ContinuumLeaf207Level : ProofLevel
literalPreferredT5ContinuumLeaf207Level = conditional
