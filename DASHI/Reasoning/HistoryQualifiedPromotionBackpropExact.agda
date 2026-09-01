module DASHI.Reasoning.HistoryQualifiedPromotionBackpropExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.TrajectoryResidueExact as Trajectory
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.LogicalPromotionExperimentBackpropExact as Promotion
import DASHI.Reasoning.LogicalConsequenceHistoryResidueExact as HistoryFixture

------------------------------------------------------------------------
-- HISTORY-QUALIFIED PROMOTION BACKPROP
--
-- Empirical path residue may permit reuse of an already-audited receipt for
-- the SAME obligation.  It never authorises a stronger promotion by itself.
-- If the path carries no such residue, the corresponding empirical design
-- search must be treated as fresh.
------------------------------------------------------------------------

data EvidenceReusePolicy : Set where
  acquireFreshEvidence
  mayReuseSameObligationEvidence
  : EvidenceReusePolicy

reusePolicy : Trajectory.ResidueFlag → EvidenceReusePolicy
reusePolicy Trajectory.residueAbsent = acquireFreshEvidence
reusePolicy Trajectory.residuePresent = mayReuseSameObligationEvidence

record HistoryQualifiedPromotionBackprop
    {proposal : PNF.ProposedPromotion}
    {demand : Promotion.EmpiricalPromotionDemand proposal}
    (bridge : Promotion.PromotionBackpropBridge demand) : Set₁ where
  constructor historyQualifiedPromotionBackprop
  field
    derivationHistory : HistoryFixture.DerivationState
    empiricalResidue : Trajectory.ResidueFlag
    residueMatchesHistory :
      empiricalResidue ≡ HistoryFixture.residue derivationHistory
    policy : EvidenceReusePolicy
    policyMatchesResidue : policy ≡ reusePolicy empiricalResidue
    sameObligationOnlyReference : String
    strongerPromotionStillNeedsEvidenceReference : String
    reauditingReference : String

open HistoryQualifiedPromotionBackprop public

logicalReconvergenceRequiresFreshEvidence :
  reusePolicy (HistoryFixture.residue HistoryFixture.reconvergedLogical)
  ≡ acquireFreshEvidence
logicalReconvergenceRequiresFreshEvidence = refl

empiricalReconvergenceMayReuseSameObligation :
  reusePolicy (HistoryFixture.residue HistoryFixture.reconvergedEmpirical)
  ≡ mayReuseSameObligationEvidence
empiricalReconvergenceMayReuseSameObligation = refl

sameFinalAssertionDoesNotDetermineReusePolicy :
  reusePolicy (HistoryFixture.residue HistoryFixture.reconvergedLogical)
  ≡ reusePolicy (HistoryFixture.residue HistoryFixture.reconvergedEmpirical) →
  ⊥
sameFinalAssertionDoesNotDetermineReusePolicy ()

record HistoryQualifiedPromotionBoundary : Set where
  constructor historyQualifiedPromotionBoundary
  field
    empiricalResidueAutomaticallySupportsStrongerPromotion : Bool
    empiricalResidueAutomaticallySupportsStrongerPromotionIsFalse :
      empiricalResidueAutomaticallySupportsStrongerPromotion ≡ false
    empiricalResidueMayPermitSameObligationReuse : Bool
    empiricalResidueMayPermitSameObligationReuseIsTrue :
      empiricalResidueMayPermitSameObligationReuse ≡ true
    residueFreeHistoryRequiresFreshEvidence : Bool
    residueFreeHistoryRequiresFreshEvidenceIsTrue :
      residueFreeHistoryRequiresFreshEvidence ≡ true
    sameFinalAssertionDeterminesReusePolicy : Bool
    sameFinalAssertionDeterminesReusePolicyIsFalse :
      sameFinalAssertionDeterminesReusePolicy ≡ false

canonicalHistoryQualifiedPromotionBoundary :
  HistoryQualifiedPromotionBoundary
canonicalHistoryQualifiedPromotionBoundary =
  historyQualifiedPromotionBoundary false refl true refl true refl false refl
