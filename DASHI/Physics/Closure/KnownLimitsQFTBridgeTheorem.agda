module DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem where

open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.UnifiedClosure as UC
open import DASHI.Physics.QFT as QFT
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB
open import DASHI.Physics.Closure.KnownLimitsFullMatterGaugeTheorem as KLMGFT
open import DASHI.Physics.Closure.KnownLimitsRecovery as KLR
open import DASHI.Physics.Closure.KnownLimitsStatus as KLS

record KnownLimitsQFTBridgeTheorem : Setω where
  field
    qftAdapter : QFT.QFTAdapter
    contractionSignatureToSpinDiracBridge :
      CSSDB.ContractionSignatureToSpinDiracBridgeTheorem
    fullMatterGaugeRecovery :
      KLMGFT.KnownLimitsFullMatterGaugeTheorem
    concreteUnification : UC.PhysicsUnification CCS.realStack
    cliffordBridge : CE.Quadratic⇒Clifford
    waveLiftEvenBridge : CE.WaveLift⇒Even
    qftRecovered :
      KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.qftLikeTheoremBacked
    recovery : KLR.KnownLimitsRecoveryWitness

canonicalKnownLimitsQFTBridgeTheorem : KnownLimitsQFTBridgeTheorem
canonicalKnownLimitsQFTBridgeTheorem =
  let
    u = CCS.physicsUnification
  in
  record
    { qftAdapter = QFT.canonicalQFTAdapter
    ; contractionSignatureToSpinDiracBridge =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; fullMatterGaugeRecovery =
        KLMGFT.canonicalKnownLimitsFullMatterGaugeTheorem
    ; concreteUnification = u
    ; cliffordBridge = UC.PhysicsUnification.q2cl u
    ; waveLiftEvenBridge = UC.PhysicsUnification.wl u
    ; qftRecovered =
        KLR.KnownLimitsRecoveryWitness.qftLikeRecovered
          KLR.canonicalKnownLimitsRecovery
    ; recovery = KLR.canonicalKnownLimitsRecovery
    }
