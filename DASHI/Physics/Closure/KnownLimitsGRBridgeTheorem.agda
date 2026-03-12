module DASHI.Physics.Closure.KnownLimitsGRBridgeTheorem where

-- Assumptions:
-- - canonical GR adapter
-- - canonical known-limits recovery witness package
--
-- Output:
-- - known-limits GR bridge theorem bundle.
--
-- Classification:
-- - known limits

open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.GR as GR
open import DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem as KLMGFT
open import DASHI.Physics.Closure.KnownLimitsRecovery as KLR
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS

record KnownLimitsGRBridgeTheorem : Setω where
  field
    grAdapter : GR.GRAdapter
    fullMatterGaugeRecovery :
      KLMGFT.KnownLimitsFullMatterGaugeTheorem
    grRecovered :
      KLS.KnownLimitsStatus.grLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.grLikeTheoremBacked
    recovery : KLR.KnownLimitsRecoveryWitness

canonicalKnownLimitsGRBridgeTheorem : KnownLimitsGRBridgeTheorem
canonicalKnownLimitsGRBridgeTheorem =
  record
    { grAdapter = GR.canonicalGRAdapter
    ; fullMatterGaugeRecovery =
        KLMGFT.canonicalKnownLimitsFullMatterGaugeTheorem
    ; grRecovered =
        KLR.KnownLimitsRecoveryWitness.grLikeRecovered
          KLR.canonicalKnownLimitsRecovery
    ; recovery = KLR.canonicalKnownLimitsRecovery
    }
