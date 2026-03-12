module DASHI.Physics.Closure.KnownLimitsQFTBridgeTheorem where

-- Assumptions:
-- - canonical QFT adapter
-- - canonical spin/Dirac, Clifford, and wave-even bridge surfaces
-- - concrete unification witnesses from real stack
--
-- Output:
-- - known-limits QFT bridge theorem bundle with canonical wave-even witnesses.
--
-- Classification:
-- - known limits

open import Agda.Primitive using (Setω)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Data.Product using (Σ; _,_)

open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ContractionQuadraticBridge as CQB
open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.UnifiedClosure as UC
open import DASHI.Physics.QFT as QFT
open import DASHI.Physics.Closure.ContractionSignatureToSpinDiracBridgeTheorem as CSSDB
open import DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem as CTEW
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
    canonicalWaveLiftEvenBridge :
      CTEW.CliffordToEvenWaveLiftBridgeTheorem
    concreteUnification : UC.PhysicsUnification CCS.realStack
    concreteContractionQuadraticBridge :
      CQB.Contraction⇒Quadratic (CB.U CCS.realStack) (CB.T CCS.realStack)
    cliffordBridge : CE.Quadratic⇒Clifford
    waveLiftEvenBridge : CE.WaveLift⇒Even

  field
    canonicalClifford :
      CE.Clifford
        (CQB.V (CQB.out concreteContractionQuadraticBridge))
        (CQB.Scalar (CQB.out concreteContractionQuadraticBridge))
    canonicalWaveLiftIntoEven :
      CE.WaveLiftIntoEven canonicalClifford
    fermionEvenLiftStructure :
      CE.WaveLiftIntoEven canonicalClifford
    physicalWaveState : Set
    physicalWaveLift :
      CE.WaveLift physicalWaveState (CE.Clifford.Cl canonicalClifford)
    physicalWaveEvenSubalgebra :
      CE.EvenSubalgebra (CE.Clifford.Cl canonicalClifford)
    physicalWaveLandsInEven :
      ∀ s →
      Σ (CE.EvenSubalgebra.Even physicalWaveEvenSubalgebra)
        (λ e →
           CE.WaveLift.lift physicalWaveLift s
             ≡
           CE.EvenSubalgebra.incl physicalWaveEvenSubalgebra e)
    gaugeCouplingStructure :
      KLMGFT.KnownLimitsFullMatterGaugeTheorem
    qftRecovered :
      KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.qftLikeTheoremBacked
    recovery : KLR.KnownLimitsRecoveryWitness

canonicalKnownLimitsQFTBridgeTheorem : KnownLimitsQFTBridgeTheorem
canonicalKnownLimitsQFTBridgeTheorem =
  let
    u = CCS.physicsUnification
    cq = UC.PhysicsUnification.cq u
    q2cl = UC.PhysicsUnification.q2cl u
    wl = UC.PhysicsUnification.wl u
    cℓ = CE.Quadratic⇒Clifford.build q2cl (CQB.out cq)
    waveIntoEven = CE.WaveLift⇒Even.build wl cℓ
  in
  record
    { qftAdapter = QFT.canonicalQFTAdapter
    ; contractionSignatureToSpinDiracBridge =
        CSSDB.canonicalContractionSignatureToSpinDiracBridgeTheorem
    ; fullMatterGaugeRecovery =
        KLMGFT.canonicalKnownLimitsFullMatterGaugeTheorem
    ; canonicalWaveLiftEvenBridge =
        CTEW.canonicalCliffordToEvenWaveLiftBridgeTheorem
    ; concreteUnification = u
    ; cliffordBridge = q2cl
    ; waveLiftEvenBridge = wl
    ; canonicalClifford = cℓ
    ; canonicalWaveLiftIntoEven = waveIntoEven
    ; fermionEvenLiftStructure = waveIntoEven
    ; physicalWaveState = CE.WaveLiftIntoEven.State waveIntoEven
    ; physicalWaveLift = CE.WaveLiftIntoEven.waveLift waveIntoEven
    ; physicalWaveEvenSubalgebra = CE.WaveLiftIntoEven.Even waveIntoEven
    ; physicalWaveLandsInEven = CE.WaveLiftIntoEven.landsInEven waveIntoEven
    ; gaugeCouplingStructure =
        KLMGFT.canonicalKnownLimitsFullMatterGaugeTheorem
    ; concreteContractionQuadraticBridge = cq
    ; qftRecovered =
        KLR.KnownLimitsRecoveryWitness.qftLikeRecovered
          KLR.canonicalKnownLimitsRecovery
    ; recovery = KLR.canonicalKnownLimitsRecovery
    }

canonicalPhysicalWaveLiftLandsInEven :
  ∀ s →
  Σ (CE.EvenSubalgebra.Even
       (KnownLimitsQFTBridgeTheorem.physicalWaveEvenSubalgebra
          canonicalKnownLimitsQFTBridgeTheorem))
    (λ e →
       CE.WaveLift.lift
         (KnownLimitsQFTBridgeTheorem.physicalWaveLift
            canonicalKnownLimitsQFTBridgeTheorem)
         s
         ≡
       CE.EvenSubalgebra.incl
         (KnownLimitsQFTBridgeTheorem.physicalWaveEvenSubalgebra
            canonicalKnownLimitsQFTBridgeTheorem)
         e)
canonicalPhysicalWaveLiftLandsInEven =
  KnownLimitsQFTBridgeTheorem.physicalWaveLandsInEven
    canonicalKnownLimitsQFTBridgeTheorem

canonicalPhysicalWaveLiftLandsInEvenOnKnownLimitsPath :
  KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
    ≡ KLS.qftLikeTheoremBacked →
  ∀ s →
  Σ (CE.EvenSubalgebra.Even
       (KnownLimitsQFTBridgeTheorem.physicalWaveEvenSubalgebra
          canonicalKnownLimitsQFTBridgeTheorem))
    (λ e →
       CE.WaveLift.lift
         (KnownLimitsQFTBridgeTheorem.physicalWaveLift
            canonicalKnownLimitsQFTBridgeTheorem)
         s
         ≡
       CE.EvenSubalgebra.incl
         (KnownLimitsQFTBridgeTheorem.physicalWaveEvenSubalgebra
            canonicalKnownLimitsQFTBridgeTheorem)
         e)
canonicalPhysicalWaveLiftLandsInEvenOnKnownLimitsPath _ =
  canonicalPhysicalWaveLiftLandsInEven
