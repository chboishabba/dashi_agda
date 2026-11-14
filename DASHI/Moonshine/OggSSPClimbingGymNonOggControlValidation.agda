module DASHI.Moonshine.OggSSPClimbingGymNonOggControlValidation where

open import DASHI.Core.Prelude

import DASHI.Moonshine.OggPrimeControlMatrixExact as Matrix
import DASHI.Moonshine.OggSSPClimbingGymEmpiricalReplayExact as Replay

------------------------------------------------------------------------
-- Regression contract added before the replay owner grows the non-Ogg rows.
-- These are the five independently typed non-Ogg controls already on master.
------------------------------------------------------------------------

p37IsExternallyNonOgg : Matrix.externalOggLabel Matrix.prime37 ≡ false
p37IsExternallyNonOgg = Matrix.prime37ExternallyNegative

p67IsExternallyNonOgg : Matrix.externalOggLabel Matrix.prime67 ≡ false
p67IsExternallyNonOgg = Matrix.prime67ExternallyNegative

p37ControlSaturates :
  Replay.controlMutualPairs Replay.p37ControlReplay ≡ Replay.replayZeroCount
p37ControlSaturates = refl

p43ControlSaturates :
  Replay.controlMutualPairs Replay.p43ControlReplay ≡ Replay.replayZeroCount
p43ControlSaturates = refl

p53ControlSaturates :
  Replay.controlMutualPairs Replay.p53ControlReplay ≡ Replay.replayZeroCount
p53ControlSaturates = refl

p61ControlSaturates :
  Replay.controlMutualPairs Replay.p61ControlReplay ≡ Replay.replayZeroCount
p61ControlSaturates = refl

p67ControlSaturates :
  Replay.controlMutualPairs Replay.p67ControlReplay ≡ Replay.replayZeroCount
p67ControlSaturates = refl

saturationIsNotOggSpecific :
  Replay.nonOggControlSaturationShowsSaturationNotOggSpecific
    Replay.canonicalClimbingGymReplayBoundary
  ≡ true
saturationIsNotOggSpecific = refl
