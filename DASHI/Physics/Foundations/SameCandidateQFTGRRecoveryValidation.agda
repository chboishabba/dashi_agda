module DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.PhysicalTheoryExperimentDiscriminationExact as Physical

------------------------------------------------------------------------
-- Focused theorem-shape regression.
--
-- This validation root intentionally does not fabricate a physical candidate.
-- It checks that the complete same-candidate receipt closes exactly the
-- Stage-6/7 promotion gate and that each consumer projection is available.
------------------------------------------------------------------------

promotionFromSameCandidateRecovery :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.SameCandidateQFTGRRecovery U →
  Physical.PhysicalPromotionGate (Weld.physicalCandidateFromUnified U)
promotionFromSameCandidateRecovery = Weld.sameCandidateRecoveryImpliesPhysicalPromotion

recoverySuppliesGR :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.SameCandidateQFTGRRecovery U →
  Physical.recoversGeneralRelativityRegime (Weld.physicalCandidateFromUnified U)
recoverySuppliesGR recovery =
  Physical.promotionRequiresGRRecovery
    (Weld.sameCandidateRecoveryImpliesPhysicalPromotion recovery)

recoverySuppliesQFT :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.SameCandidateQFTGRRecovery U →
  Physical.recoversLowEnergyQuantumFieldRegime (Weld.physicalCandidateFromUnified U)
recoverySuppliesQFT recovery =
  Physical.promotionRequiresQFTRecovery
    (Weld.sameCandidateRecoveryImpliesPhysicalPromotion recovery)

recoverySuppliesNovelObservable :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.SameCandidateQFTGRRecovery U →
  Physical.novelObservable (Weld.physicalCandidateFromUnified U)
recoverySuppliesNovelObservable recovery =
  Physical.promotionRequiresNovelObservable
    (Weld.sameCandidateRecoveryImpliesPhysicalPromotion recovery)

recoverySuppliesFalsifiableMeasurement :
  ∀ {U : Weld.UnifiedCandidate} →
  Weld.SameCandidateQFTGRRecovery U →
  Physical.falsifiableMeasurement (Weld.physicalCandidateFromUnified U)
recoverySuppliesFalsifiableMeasurement recovery =
  Physical.promotionRequiresFalsifiableMeasurement
    (Weld.sameCandidateRecoveryImpliesPhysicalPromotion recovery)
