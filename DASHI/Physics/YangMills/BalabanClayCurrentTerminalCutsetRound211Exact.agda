{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound211Exact where

------------------------------------------------------------------------
-- ROUND211: EXPECTATION-LINKED CONTINUUM ROUTE
--
-- Introspective correction of Round210.
--
-- The preferred T5 expectation producer already carries one continuum measure
-- and tail-controlled convergence of selected diagonal expectations to that
-- exact target.  The preferred OS-Gram compiler shares the target by refl.
-- Therefore global measure compact containment / Prokhorov is NOT a prerequisite
-- on this producer route.  It remains a compatibility existence route for a
-- producer which does not already supply the continuum measure.
--
-- The live continuum link is instead:
--
--   selected determining/bounded observable F
--      -> E_{mu_n}[F] converges to E_{mu_infty}[F]
--
-- together with the finite expectation semantics needed to close normalization,
-- positivity and action/gauge invariance directly at the scalar level.
--
-- A second downstream firewall is recorded here: OS reconstruction and positive
-- spectral gap are distinct.  The preferred route must use the repository's
-- separated reconstruction / clustering-gap surfaces rather than a legacy
-- wrapper whose reconstructed-theory carrier already contains gap positivity.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; _∷_; [])

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayCurrentTerminalCutsetRound210Exact as R210
import DASHI.Physics.YangMills.BalabanClayT5DirectExpectationPropertyClosureExact as Direct
import DASHI.Physics.YangMills.BalabanClayT5ExpectationLinkedContinuumOSExact as Linked
import DASHI.Physics.YangMills.BalabanClayT5SelectedMomentCompactContainmentExact as Compactness
import DASHI.Physics.YangMills.BalabanClayT5SelectedProkhorovExtractionExact as Prokhorov
import DASHI.Physics.YangMills.BalabanOSReconstructionMassGapProduction as Production
import DASHI.Physics.YangMills.YMOperatorDomainContinuumFrontier2026Exact as Frontier

data T5PreferredContinuumLeaf211 : Set where
  -- Shared normalization/positivity/action + continuum-link representation seam.
  physicalSelectedExpectationPropertyAndDeterminingTestMeaning :
    T5PreferredContinuumLeaf211

  -- Remaining selected continuum Schwinger properties/semantics.
  physicalContinuumEuclideanCovariance : T5PreferredContinuumLeaf211
  physicalContinuumSymmetry : T5PreferredContinuumLeaf211
  physicalContinuumTemperedness : T5PreferredContinuumLeaf211
  physicalContinuumRegularity : T5PreferredContinuumLeaf211
  physicalContinuumClustering : T5PreferredContinuumLeaf211
  physicalGramReflectionToSchwingerReflectionMeaning : T5PreferredContinuumLeaf211

  -- Same-object semantic adapter into the correctly separated OS reconstruction
  -- carrier.  Reconstruction itself is standard; a positive gap remains a later
  -- clustering/spectral theorem and is not included here.
  physicalExpectationLinkedSchwingerSystemMeaning : T5PreferredContinuumLeaf211

preferredT5ContinuumCut211 : List T5PreferredContinuumLeaf211
preferredT5ContinuumCut211 =
  physicalSelectedExpectationPropertyAndDeterminingTestMeaning ∷
  physicalContinuumEuclideanCovariance ∷
  physicalContinuumSymmetry ∷
  physicalContinuumTemperedness ∷
  physicalContinuumRegularity ∷
  physicalContinuumClustering ∷
  physicalGramReflectionToSchwingerReflectionMeaning ∷
  physicalExpectationLinkedSchwingerSystemMeaning ∷ []

directExpectationPropertyClosureLevel : ProofLevel
directExpectationPropertyClosureLevel =
  Direct.directExpectationPropertyClosureCompilerLevel

expectationLinkedContinuumOSLevel : ProofLevel
expectationLinkedContinuumOSLevel = Linked.expectationLinkedContinuumOSCarrierLevel

selectedDeterminingExpectationConvergenceLevel : ProofLevel
selectedDeterminingExpectationConvergenceLevel =
  Linked.expectationLinkedContinuumOSAxiomAssemblyLevel

-- Compatibility route retained but not charged to the preferred producer path.
selectedMomentCompactContainmentCompatibilityLevel : ProofLevel
selectedMomentCompactContainmentCompatibilityLevel =
  Compactness.selectedMomentCompactContainmentCompilerLevel

selectedProkhorovCompatibilityLevel : ProofLevel
selectedProkhorovCompatibilityLevel = Prokhorov.selectedProkhorovExtractionCompilerLevel

prokhorovCompactnessNotRequiredByPreferredExpectationProducerRoute : Bool
prokhorovCompactnessNotRequiredByPreferredExpectationProducerRoute = true

legacyPositiveGapInsideReconstructionNotUsedByPreferredRoute : Bool
legacyPositiveGapInsideReconstructionNotUsedByPreferredRoute = true

standardOSReconstructionKeptSeparateFromGap : ProofLevel
standardOSReconstructionKeptSeparateFromGap = Production.osReconstructionLevel

data PreferredFirstPrerequisiteStatus211 : Set where
  missingSelectedExpectationPropertyAndDeterminingTestMeaning :
    PreferredFirstPrerequisiteStatus211
  readyForExpectationLinkedContinuumPropertyCompiler :
    PreferredFirstPrerequisiteStatus211

preferredCurrentStatus211 : PreferredFirstPrerequisiteStatus211
preferredCurrentStatus211 =
  missingSelectedExpectationPropertyAndDeterminingTestMeaning

round210GlobalCompactnessIsCompatibilityOnlyOnPreferredProducer : Bool
round210GlobalCompactnessIsCompatibilityOnlyOnPreferredProducer = true

round210AuditRetained : ProofLevel
round210AuditRetained = R210.currentYMTerminalCutsetRound210Level

finiteToContinuumYMStillOpen :
  Frontier.finiteToContinuumYMConstructionClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
finiteToContinuumYMStillOpen = refl

continuumOSWightmanStillOpen :
  Frontier.continuumOSWightmanPackageClosed
    Frontier.canonicalYMOperatorContinuumFrontier ≡ false
continuumOSWightmanStillOpen = refl

currentYMTerminalCutsetRound211Level : ProofLevel
currentYMTerminalCutsetRound211Level = machineChecked

literalPreferredT5ContinuumLeaf211Level : ProofLevel
literalPreferredT5ContinuumLeaf211Level = conditional
