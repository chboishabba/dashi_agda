module DASHI.Physics.Foundations.YMEMForceGravityFilsingerSameOriginalPhysicalCutExact where

-- Source-native P1 cut. Physical evidentiary apparatus remains separate:
-- an EM gauge method can be shared by different devices without their
-- histories, materials, stress tensors, source ports or measurements being
-- identified.
--
-- Filsinger: existing KSW668 full-vector Maxwell jet + EXACT ORIGINAL
-- FiniteVolume Maxwell faces + selected Filsinger port + same cap, all indexed
-- by one (b, f, s). Do not fabricate the E/H surface work identity or a
-- measured source merely because a pointwise Poynting theorem holds.
--
-- Gravity: original force-only, four-channel/TT, superconducting
-- source-vs-constitutive, and source-specific ordinary-GR closure machinery.
-- Actual external free-fall / clock / metric data are still required.
--
-- YM: original SU2 Cartan U1 Lie bracket zero is the classical gauge method.
-- No positive Maxwell photon mass nor continuum non-Abelian OS gap inferred.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Primitive using (Level; _⊔_; lsuc; lzero)

import DASHI.Physics.Electromagnetism.U1AsSU2AbelianRestrictionExact as U1
import DASHI.Physics.Electromagnetism.U1ElectromagneticApplicationExact as EM
import DASHI.Physics.Electromagnetism.RightHandRule369Exact as RightEM
import DASHI.Physics.Foundations.OrientedBracketEMYMNS369Regression as SharedOrientation
import DASHI.Physics.YangMills.BalabanSU2LieAlgebraCarrier as SU2
import DASHI.Physics.YangMills.BalabanSU2LieBracket as Bracket
import DASHI.Physics.ExoticGravity.AntigravitySameStateFourChannelDiscriminatorExact as Four
import DASHI.Physics.ExoticGravity.AntigravityExperimentPortfolioExact as Portfolio
import DASHI.Physics.ExoticGravity.SuperconductingGravityExperimentDesignProofSearchCrossPollinationExact as SC
import DASHI.Physics.ExoticGravity.SuperconductingGravityCouplingResidualBidiExact as Residual
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryGRComparatorCompilationExact as GR
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryBackgroundClosureExact as Background
import DASHI.Physics.ExoticGravity.AntigravityLaboratoryOrdinaryModelClosureWeldExact as Ordinary
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Plasma.KSW668FullVectorMaxwellJetExact as KSW
import DASHI.Physics.Motors.SmithFilsingerFullVectorPoyntingPortWeldExact as Poynting
import DASHI.Physics.Motors.SmithFilsingerFiniteVolumeMaxwellBoundaryWeldExact as Finite
import DASHI.Physics.Motors.SmithFilsingerSpatialSourceBoundaryWeldExact as Spatial
import DASHI.Physics.Motors.SmithFilsingerSourceMaxwellBoundaryWeldExact as Source
import DASHI.Physics.Motors.SmithFilsingerMidpointPhaseWorkExact as Port
import DASHI.Physics.Motors.SmithFilsingerReplenishedCycleCapExact as Cycle
import DASHI.Physics.Motors.Circuit36927RecoveryEnergyBoundExact as Bound

------------------------------------------------------------------------
-- F1. Stronger SAME original Filsinger boundary. Both the differential
-- Maxwell jet and the actual mesh belong to the same b/f/s model.
-- Each original physical Poynting/port admission is CONTENTFUL and must
-- be provided by a real source. No unrestricted Set tokens added here.
------------------------------------------------------------------------

record SameOriginalFilsingerFullVectorAndFiniteMesh
  {r : Level} {F : C3.RealField r}
  (jet : KSW.FullVectorMaxwellJet F)
  (b : Source.SelectedBoundary)
  (f : Source.FormalFieldToPort b)
  (s : Source.SignedSourceCycleWeld b f)
  : Set (lsuc (r ⊔ (lsuc (lsuc lzero)))) where
  field
    integratedPhysicalVector :
      Poynting.SameOriginalPhysicalFieldBoundary jet b f s
    realSelectedFiniteMesh :
      Finite.OriginalFiniteVolumeAdmission b f

open SameOriginalFilsingerFullVectorAndFiniteMesh

-- The actual original face->cell->spatial-chain->port proof is reused,
-- with equality of original b and f ensured by the dependent type.
selectedRealMeshToOriginalPort :
  ∀ {r} {F : C3.RealField r}
  (jet : KSW.FullVectorMaxwellJet F)
  (b : Source.SelectedBoundary)
  (f : Source.FormalFieldToPort b)
  (s : Source.SignedSourceCycleWeld b f) →
  SameOriginalFilsingerFullVectorAndFiniteMesh jet b f s →
  Spatial.SpatialToOriginalSourcePort b f
selectedRealMeshToOriginalPort jet b f s w =
  Finite.asExistingOriginalSpatialWeld b f (realSelectedFiniteMesh w)

-- Both the original finite mesh/port and source-specific matching premise
-- are explicit inputs; conservation at the original terminals is derived
-- by the existing theorem, not postulated as a brand-new energy ledger.
selectedRealMeshClosesOriginalSignedPort :
  ∀ {r} {F : C3.RealField r}
  (jet : KSW.FullVectorMaxwellJet F)
  (b : Source.SelectedBoundary)
  (f : Source.FormalFieldToPort b)
  (s : Source.SignedSourceCycleWeld b f) →
  (w : SameOriginalFilsingerFullVectorAndFiniteMesh jet b f s) →
  (Port.MidpointTwoPortWorkWindow.naturalIncident
      (Source.FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.controllerIncident
      (Source.FormalFieldToPort.portWindow f))
    + Port.MidpointTwoPortWorkWindow.initialStored
      (Source.FormalFieldToPort.portWindow f)
  ≡ (Port.MidpointTwoPortWorkWindow.naturalOutgoing
      (Source.FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.controllerOutgoing
      (Source.FormalFieldToPort.portWindow f))
    + (Port.MidpointTwoPortWorkWindow.usefulWork
      (Source.FormalFieldToPort.portWindow f)
    + (Port.MidpointTwoPortWorkWindow.internalLoss
      (Source.FormalFieldToPort.portWindow f)
    + Port.MidpointTwoPortWorkWindow.finalStored
      (Source.FormalFieldToPort.portWindow f)))
selectedRealMeshClosesOriginalSignedPort jet b f s w =
  Finite.finiteVolumeClosesSameOriginalSignedPorts b f
    (realSelectedFiniteMesh w)

-- Independently selected natural-source cap is not discarded on the
-- original port, even when the local field is organized differently.
selectedRealMeshStillPaysOriginalNaturalCap :
  ∀ {r} {F : C3.RealField r}
  (jet : KSW.FullVectorMaxwellJet F)
  (b : Source.SelectedBoundary)
  (f : Source.FormalFieldToPort b)
  (s : Source.SignedSourceCycleWeld b f) →
  SameOriginalFilsingerFullVectorAndFiniteMesh jet b f s →
  Bound._≤_
    (Port.MidpointTwoPortWorkWindow.usefulWork
      (Source.FormalFieldToPort.portWindow f))
    (Cycle.AdmittedSourceCapCycle.independentlyAdmittedNaturalCap
      (Source.SignedSourceCycleWeld.cycleWithSourceCap s)
      + Cycle.RepeatableSourceCycle.controllerWork
        (Cycle.AdmittedSourceCapCycle.repeatable
          (Source.SignedSourceCycleWeld.cycleWithSourceCap s)))
selectedRealMeshStillPaysOriginalNaturalCap jet b f s w =
  Source.sourceCapTransfersToSameOriginalPort b f s

-- Original pointwise full 3D Poynting is preserved; its INTEGRATION is
-- the separate required SameOriginalPhysicalFieldBoundary field above.
sourceMaxwellCurlStillGivesLocalPoynting :
  ∀ {r} {F : C3.RealField r}
  (jet : KSW.FullVectorMaxwellJet F) →
  KSW.fullVectorSignedBudget jet ≡ C3.zero F
sourceMaxwellCurlStillGivesLocalPoynting =
  Poynting.threeComponentPoyntingFromOriginalMaxwell

------------------------------------------------------------------------
-- G1. Use preexisting antigravity tests, NOT a newly invented outcome.
-- Weight-only is not a free-fall or metric discriminator, even with
-- a Maxwell model that fits every measured support-force datum.
------------------------------------------------------------------------

ordinaryForceSignature : Four.MechanismSignature
ordinaryForceSignature = Four.signature Four.ordinaryForceConfounder

ordinaryEMSupportCanHaveWeightSignal :
  Four.supportWeightChannel ordinaryForceSignature ≡ true
ordinaryEMSupportCanHaveWeightSignal = refl

ordinaryEMSupportDoesNotByItselfSupplyFreeFall :
  Four.freeFallMetricChannel ordinaryForceSignature ≡ false
ordinaryEMSupportDoesNotByItselfSupplyFreeFall = refl

ordinaryEMSupportDoesNotByItselfSupplyClock :
  Four.clockMetricChannel ordinaryForceSignature ≡ false
ordinaryEMSupportDoesNotByItselfSupplyClock = refl

ordinaryEMSupportDoesNotByItselfSupplyOpticalMetric :
  Four.opticalMetricChannel ordinaryForceSignature ≡ false
ordinaryEMSupportDoesNotByItselfSupplyOpticalMetric = refl

ordinaryEMSupportDoesNotByItselfSupplyTT :
  Four.propagatingTTChannel ordinaryForceSignature ≡ false
ordinaryEMSupportDoesNotByItselfSupplyTT = refl

selectedFourChannelMetricTestStillRequiresItsOwnCandidate :
  Portfolio.metricVsNonmetric
    (Portfolio.coverage Portfolio.matchedFourChannelExperiment) ≡ true
selectedFourChannelMetricTestStillRequiresItsOwnCandidate =
  Portfolio.matchedFourChannelCoversMetricDiscrimination

sameCoarseApparentSignalStillConfoundsSourceVsConstitutive :
  SC.coarseSignalObserver SC.sourceOnlyWorld
    ≡ SC.coarseSignalObserver SC.constitutiveExcessWorld
sameCoarseApparentSignalStillConfoundsSourceVsConstitutive = refl

-- Existing consumer's actual first missing evidence leaf, no bogus
-- gravitational anomalous coefficient manufactured from EM lift.
originalSuperconductingGravityAlphaFrontier :
  Residual.AlphaLeaf
originalSuperconductingGravityAlphaFrontier =
  Residual.currentFirstOpenAlphaLeaf

originalSuperconductingGravityAlphaStartsWithSourceObservable :
  originalSuperconductingGravityAlphaFrontier
    ≡ Residual.sourceObservableLeaf
originalSuperconductingGravityAlphaStartsWithSourceObservable = refl

-- A completed ordinary GR comparator and laboratory EM/background
-- closure are stronger than a static force or a model signature; only
-- the source-scoped ORDINARY model receipt may be unwrapped.
originalOrdinaryGRBackgroundClosure :
  (prediction : GR.OrdinaryGRPredictionReceipt) →
  Ordinary.TypedOrdinaryModelClosureWeld prediction →
  Background.SameApparatusBackgroundClosureReceipt prediction
originalOrdinaryGRBackgroundClosure prediction w =
  Ordinary.TypedOrdinaryModelClosureWeld.typedBackgroundClosure w

-- Original YM U1 mathematical zero-bracket is a source-owned METHOD
-- shared by Filsinger and gravity. It is NOT a nonzero photon mass.
selectedAbelianGaugeAlgebra :
  (a b : U1.U1LieAlgebra) →
  Bracket.lieBracket (U1.embedU1Lie a) (U1.embedU1Lie b)
    ≡ SU2.lieZero
selectedAbelianGaugeAlgebra = U1.u1EmbeddedLieBracketZero

ordinaryEMRealCalibrationStillRequired :
  EM.applicationReductionNeedsIndependentValidation
    EM.canonicalU1ElectromagneticBoundary ≡ true
ordinaryEMRealCalibrationStillRequired =
  EM.U1ElectromagneticBoundary.applicationReductionNeedsIndependentValidationIsTrue


-- The actual 369 EM/YM orientation owner is a more informative reuse than
-- another nominal "EM is YM" statement.  Poynting E×H, Lorentz qv×B,
-- current-force Iℓ×B and magnetic torque μ×B share a signed skeleton;
-- they are NOT the same physical observable or field source.
sourceNativeEMYMRightHandOrientation :
  RightEM.RightHandRule369Boundary.rightHandRuleUsesShared369Orientation
    RightEM.canonicalRightHandRule369Boundary ≡ true
sourceNativeEMYMRightHandOrientation = refl

sourceNativeSharedOrientationDoesNotIdentifyForceAndFlux :
  RightEM.RightHandRule369Boundary.sharedOrientationIdentifiesPhysicalObservable
    RightEM.canonicalRightHandRule369Boundary ≡ false
sourceNativeSharedOrientationDoesNotIdentifyForceAndFlux = refl

sourceNativeYMStillHasUnpaidRecoveryC3Seam :
  SharedOrientation.ymUnifiedRecoveryC3StillGated ≡ false
sourceNativeYMStillHasUnpaidRecoveryC3Seam =
  SharedOrientation.ymUnifiedRecoveryC3StillGated
