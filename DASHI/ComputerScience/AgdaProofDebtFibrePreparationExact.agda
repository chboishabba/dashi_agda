module DASHI.ComputerScience.AgdaProofDebtFibrePreparationExact where

------------------------------------------------------------------------
-- PROOF-DEBT ROUTER × AGDA ELABORATION ADAPTER
--
-- This is deliberately not a second scheduler.
--
--   ProofDebtRouterExact decides whether work is mathematics, transcription,
--   evidence, local Agda certification, external Lean, Aristotle, or closed.
--
--   AgdaElaborationResidencyComplexityExact only refines the runLocalAgda
--   case by selecting the preparation needed before re-entering the checker.
--
-- In particular, a conversion/residency hotspot on a large carrier is routed
-- through the already-owned fibre abstraction discipline: prove the atomic
-- relation, lift it through a preservation receipt, and continue on the coarse
-- observed coordinates.  Resource pressure never changes theorem status.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.ProofDebtRouterExact as Debt
import DASHI.Core.AtomicGlobalFibreLiftExact as FibreLift
import DASHI.ComputerScience.AgdaElaborationResidencyComplexityExact as Elab

data LocalAgdaPreparation : Set where
  directLocalCheck
  liftThroughFibreBeforeCheck
  splitInferenceBeforeCheck
  shareIntermediateTermsBeforeCheck
  interfaceConeSurgeryBeforeCheck
  notLocalAgdaAction : LocalAgdaPreparation

prepareLocalAgda :
  Debt.SchedulerAction → Elab.ElaborationObservation → LocalAgdaPreparation
prepareLocalAgda Debt.runLocalAgda observation
  with Elab.selectIntervention observation
... | Elab.stageEqualityOrConversion = liftThroughFibreBeforeCheck
... | Elab.exposeIndicesAndSplitInference = splitInferenceBeforeCheck
... | Elab.nameAndShareIntermediateTerms = shareIntermediateTermsBeforeCheck
... | Elab.performInterfaceConeSurgery = interfaceConeSurgeryBeforeCheck
... | Elab.noElaborationSurgerySelected = directLocalCheck
prepareLocalAgda _ observation = notLocalAgdaAction

------------------------------------------------------------------------
-- The adapter preserves ownership: non-local routes are not silently turned
-- back into local Agda work by elaboration profiling.
------------------------------------------------------------------------

externalLeanRemainsExternal : ∀ observation →
  prepareLocalAgda Debt.sendExternalLean observation ≡ notLocalAgdaAction
externalLeanRemainsExternal observation = refl

aristotleRemainsExternal : ∀ observation →
  prepareLocalAgda Debt.sendAristotleLean observation ≡ notLocalAgdaAction
aristotleRemainsExternal observation = refl

novelMathematicsRemainsMathematics : ∀ observation →
  prepareLocalAgda Debt.researchMathematics observation ≡ notLocalAgdaAction
novelMathematicsRemainsMathematics observation = refl

------------------------------------------------------------------------
-- Concrete elaboration-control fixtures.
------------------------------------------------------------------------

zeroProfile : Elab.ElaborationProfile
zeroProfile = Elab.elaborationProfile 0 0 0 0 0 0 0 0

conversionResidencyHotspot : Elab.ElaborationObservation
conversionResidencyHotspot =
  Elab.elaborationObservation zeroProfile true true false false false

metaResidencyHotspot : Elab.ElaborationObservation
metaResidencyHotspot =
  Elab.elaborationObservation zeroProfile true false true false false

sharingHotspot : Elab.ElaborationObservation
sharingHotspot =
  Elab.elaborationObservation zeroProfile false false false true false

coneHotspot : Elab.ElaborationObservation
coneHotspot =
  Elab.elaborationObservation zeroProfile false false false false true

cheapLocalObservation : Elab.ElaborationObservation
cheapLocalObservation =
  Elab.elaborationObservation zeroProfile false false false false false

conversionHotspotUsesFibreBoundaryFirst :
  prepareLocalAgda Debt.runLocalAgda conversionResidencyHotspot
  ≡ liftThroughFibreBeforeCheck
conversionHotspotUsesFibreBoundaryFirst = refl

metaHotspotSplitsInferenceFirst :
  prepareLocalAgda Debt.runLocalAgda metaResidencyHotspot
  ≡ splitInferenceBeforeCheck
metaHotspotSplitsInferenceFirst = refl

sharingHotspotNamesTermsFirst :
  prepareLocalAgda Debt.runLocalAgda sharingHotspot
  ≡ shareIntermediateTermsBeforeCheck
sharingHotspotNamesTermsFirst = refl

coneHotspotCutsInterfaceFirst :
  prepareLocalAgda Debt.runLocalAgda coneHotspot
  ≡ interfaceConeSurgeryBeforeCheck
coneHotspotCutsInterfaceFirst = refl

cheapLocalWorkChecksDirectly :
  prepareLocalAgda Debt.runLocalAgda cheapLocalObservation
  ≡ directLocalCheck
cheapLocalWorkChecksDirectly = refl

------------------------------------------------------------------------
-- Fibre-native firewall.
--
-- `liftThroughFibreBeforeCheck` does not mean "assume the global theorem".
-- The actual theorem-producing API remains FibreRelationLift /
-- atomicRelationFamilyToGlobal.  This adapter only schedules that existing
-- proof shape before checker re-entry.
------------------------------------------------------------------------

record ProofDebtElaborationFibreBoundary : Set where
  constructor proof-debt-elaboration-fibre-boundary
  field
    elaborationProfileChangesMathematicalStatus : Bool
    elaborationProfileChangesSourceAlignment : Bool
    fibreCompressionManufacturesGlobalTruth : Bool
    relationPreservationReceiptStillRequired : Bool
    nonLocalBackendMayBeReopenedLocallyByProfiler : Bool
    localConversionHotspotMayRequestFibreCompression : Bool

canonicalProofDebtElaborationFibreBoundary : ProofDebtElaborationFibreBoundary
canonicalProofDebtElaborationFibreBoundary =
  proof-debt-elaboration-fibre-boundary
    false false false true false true

-- Keep the generic relation-lift owner in the type dependency of this adapter:
-- the preparation action is specifically about using this existing API rather
-- than inventing a separate atomic/global inference rule.
relationLiftOwnerAvailable :
  ∀ {Index Atomic Global : Set}
    {AtomicRel : Atomic → Atomic → Set}
    {GlobalRel : Global → Global → Set}
    {observe : (Index → Atomic) → Global} →
  FibreLift.FibreRelationLift AtomicRel GlobalRel observe →
  FibreLift.FibreRelationLift AtomicRel GlobalRel observe
relationLiftOwnerAvailable lift = lift
