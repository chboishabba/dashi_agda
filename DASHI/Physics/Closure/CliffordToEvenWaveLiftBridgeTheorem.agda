module DASHI.Physics.Closure.CliffordToEvenWaveLiftBridgeTheorem where

-- Canonical theorem source for the WaveLift=>Even bridge on the closure path.
-- Keep downstream users pointed here rather than
-- DASHI.Physics.WaveLiftEvenSubalgebra.

open import Agda.Primitive using (Setω)

open import DASHI.Physics.CliffordEvenLiftBridge as CE
open import DASHI.Physics.Closure.CanonicalContractionToCliffordBridgeTheorem as CCTCB

record CliffordToEvenWaveLiftBridgeTheorem : Setω where
  field
    canonicalBridge : CCTCB.CanonicalContractionToCliffordBridgeTheorem
    cliffordBridge : CE.Quadratic⇒Clifford
    waveLiftEvenBridge : CE.WaveLift⇒Even
    waveLiftIntoEven :
      ∀ {V Scalar} (Cℓ : CE.Clifford V Scalar) →
      CE.WaveLiftIntoEven Cℓ

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
  in
  record
    { canonicalBridge = canonicalBridge
    ; cliffordBridge = cliffordBridge
    ; waveLiftEvenBridge = waveLiftEvenBridge
    ; waveLiftIntoEven = CE.WaveLift⇒Even.build waveLiftEvenBridge
    }
