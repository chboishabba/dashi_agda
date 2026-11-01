module DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryValidation where

import DASHI.Physics.Foundations.SameCandidateQFTGRRecoveryExact as Weld
import DASHI.Physics.Foundations.SharedEffectiveSourceRecoveryExact as Source

------------------------------------------------------------------------
-- Focused regression: the shared-source factorisations compile to exactly the
-- two cross-sector receipts consumed by the same-candidate recovery theorem.
------------------------------------------------------------------------

sharedSourceProducesStressWeld :
  ∀ {U : Weld.UnifiedCandidate} →
  Source.SharedSourceCrossSectorReceipt U →
  Weld.SameStressEnergyWeld U
sharedSourceProducesStressWeld receipt =
  proj₁ (Source.sharedSourceCrossSectorReceiptCompiles receipt)

sharedSourceProducesCommonRegime :
  ∀ {U : Weld.UnifiedCandidate} →
  Source.SharedSourceCrossSectorReceipt U →
  Weld.CommonRegimeRecovery U
sharedSourceProducesCommonRegime receipt =
  proj₂ (Source.sharedSourceCrossSectorReceiptCompiles receipt)

sharedSourceFactorisationsCloseStressEquality :
  ∀ {U : Weld.UnifiedCandidate}
    (source : Source.SharedEffectiveSourceTheory U) →
  Source.GRSourceFactorisation source →
  Source.QFTSourceFactorisation source →
  Weld.StressEnergyWeldToken U →
  Weld.SameStressEnergyWeld U
sharedSourceFactorisationsCloseStressEquality =
  Source.sharedSourceImpliesSameStressEnergy
