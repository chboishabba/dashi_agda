{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalValidation where

-- RED validation for the current-master terminal route.
-- The final preferred path should consume the least-privilege R387 direct
-- selected mixed-log upper, not require the optional R410 factor replay.

import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

finalDirectUpperCompilerWritten : Final.finalDirectUpperCompilerWritten ≡ true
finalDirectUpperCompilerWritten = Final.finalDirectUpperCompilerWrittenIsTrue

r410MandatoryForTerminalGapIsFalse : Final.r410MandatoryForTerminalGap ≡ false
r410MandatoryForTerminalGapIsFalse = Final.r410MandatoryForTerminalGapIsFalse
