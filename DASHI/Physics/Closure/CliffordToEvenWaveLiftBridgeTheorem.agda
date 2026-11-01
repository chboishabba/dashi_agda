module DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem where

-- Canonical theorem source for the WaveLift=>Even bridge on the closure path.
-- Keep downstream users pointed here rather than
-- DASHI.Physics.WaveLiftEvenSubalgebra.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.ClosureBuilder as CB
open import DASHI.Physics.ConcreteClosureStack as CCS
open import DASHI.Physics.ContractionQuadraticBridge as CQB
open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.Closure.CanonicalContractionToCliffordBridgeTheorem as CCTCB

record CliffordToEvenWaveLiftBridgeTheorem : Setω where
  field
    canonicalBridge : CCTCB.CanonicalContractionToCliffordBridgeTheorem
    cliffordBridge : CE.Quadratic⇒Clifford
    waveLiftEvenBridge : CE.WaveLift⇒Even
    contractionQuadraticBridge :
      CQB.Contraction⇒Quadratic (CB.U CCS.realStack) (CB.T CCS.realStack)
    canonicalCliffordFromContractionQuadratic :
      CE.Clifford
        (CQB.V (CQB.out contractionQuadraticBridge))
        (CQB.Scalar (CQB.out contractionQuadraticBridge))
    waveLiftIntoEven :
      ∀ {V Scalar} (Cℓ : CE.Clifford V Scalar) →
      CE.WaveLiftIntoEven Cℓ
    canonicalWaveLiftIntoEvenFromContractionQuadratic :
      CE.WaveLiftIntoEven canonicalCliffordFromContractionQuadratic

canonicalCliffordToEvenWaveLiftBridgeTheorem :
  CliffordToEvenWaveLiftBridgeTheorem
canonicalCliffordToEvenWaveLiftBridgeTheorem =
  let
    canonicalBridge = CCTCB.canonicalContractionToCliffordBridgeTheorem
    cliffordBridge =
      CCTCB.CanonicalContractionToCliffordBridgeTheorem.concreteCliffordBridge
        canonicalBridge
    waveLiftEvenBridge =
      CCTCB.CanonicalContractionToCliffordBridgeTheorem.concreteWaveLiftEvenBridge
        canonicalBridge
    contractionQuadraticBridge =
      CCTCB.CanonicalContractionToCliffordBridgeTheorem.concreteContractionQuadraticBridge
        canonicalBridge
    canonicalCliffordFromContractionQuadratic =
      CCTCB.CanonicalContractionToCliffordBridgeTheorem.concreteCliffordFromCanonicalQuadratic
        canonicalBridge
  in
  record
    { canonicalBridge = canonicalBridge
    ; cliffordBridge = cliffordBridge
    ; waveLiftEvenBridge = waveLiftEvenBridge
    ; contractionQuadraticBridge = contractionQuadraticBridge
    ; canonicalCliffordFromContractionQuadratic =
        canonicalCliffordFromContractionQuadratic
    ; waveLiftIntoEven = CE.WaveLift⇒Even.build waveLiftEvenBridge
    ; canonicalWaveLiftIntoEvenFromContractionQuadratic =
        CE.WaveLift⇒Even.build
          waveLiftEvenBridge
          canonicalCliffordFromContractionQuadratic
    }
