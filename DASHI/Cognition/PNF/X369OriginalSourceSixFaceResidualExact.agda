module DASHI.Cognition.PNF.X369OriginalSourceSixFaceResidualExact where

-- Original Leech-LILA: Anatolii Kornienko; DASHI extension.
-- Six faces are an ORIGINAL RECURRENT SOURCE CONTROL cube, not
-- automatically the spatial H07 native graph or physical nine-DOF flow.
-- Source-written only: kernel acceptance deliberately deferred.
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
import DASHI.Cognition.PNF.X369InputIndexedFutureConsumerExact as Future

data Face : Set where
  xy0 xy1 xz0 xz1 yz0 yz1 : Face

module Source {Input State Residual Output : Set}
  (x y z : Input)
  (step : Input → State → State)
  (observe : Input → State → Output)
  -- A source-specific difference/reconstruction operator: for native
  -- byte histories, use saved left bytes plus XOR difference. The finite
  -- hyperfabric appraisal fibre need not be this Residual carrier.
  (difference : State → State → Residual)
  (rebuild : State → Residual → State)
  (rebuildCorrect : (a b : State) →
    rebuild a (difference a b) ≡ b) where

  run : List Input → State → State
  run [] s = s
  run (u ∷ us) s = run us (step u s)

  left : Face → List Input
  left xy0 = x ∷ y ∷ []
  left xy1 = z ∷ x ∷ y ∷ []
  left xz0 = x ∷ z ∷ []
  left xz1 = y ∷ x ∷ z ∷ []
  left yz0 = y ∷ z ∷ []
  left yz1 = x ∷ y ∷ z ∷ []

  right : Face → List Input
  right xy0 = y ∷ x ∷ []
  right xy1 = z ∷ y ∷ x ∷ []
  right xz0 = z ∷ x ∷ []
  right xz1 = y ∷ z ∷ x ∷ []
  right yz0 = z ∷ y ∷ []
  right yz1 = x ∷ z ∷ y ∷ []

  sourceLeft : Face → State → State
  sourceLeft f s = run (left f) s

  sourceRight : Face → State → State
  sourceRight f s = run (right f) s

  faceResidual : Face → State → Residual
  faceResidual f s = difference (sourceLeft f s) (sourceRight f s)

  -- Exact original-right endpoint reopens from retained left and
  -- residual even when the two native control paths DO NOT commute.
  faceBidi : (f : Face) (s : State) →
    rebuild (sourceLeft f s) (faceResidual f s) ≡ sourceRight f s
  faceBidi f s =
    rebuildCorrect (sourceLeft f s) (sourceRight f s)

  -- Face commutation is a separately evidenced SOURCE hypothesis.
  -- No claim that differing control order gives equal path observations.
  module Compatible
    (commuting : (f : Face) (s : State) →
      sourceLeft f s ≡ sourceRight f s) where

    sameEndpointConsumer : (probe : Input) (f : Face) (s : State) →
      observe probe (sourceLeft f s) ≡
      observe probe (sourceRight f s)
    sameEndpointConsumer probe f s =
      Future.cong (observe probe) (commuting f s)

  -- Conditional arbitrary-future consumer agreement for each true face.
  module FutureCompatible
    (commuting : (f : Face) (s : State) →
      sourceLeft f s ≡ sourceRight f s) where

    allFutureProbes : (inputs : List Input) (f : Face) (s : State) →
      Future.trace step observe inputs (sourceLeft f s) ≡
      Future.trace step observe inputs (sourceRight f s)
    allFutureProbes inputs f s =
      Future.cong (Future.trace step observe inputs) (commuting f s)

-- Source-owned native step, bytes, readout, control orientation and
-- checkpoint provenance remain real implementation premises. The six
-- faces of GovernedIndexedResidualCubeExact retain their own indexed
-- typed vertices and independent obligations; no carrier equality here.
