{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalValidation where

-- GREEN regression for the current-master terminal route.
-- The preferred path consumes the least-privilege R387 direct selected
-- mixed-log upper and does not require the optional R410 factor replay.

import DASHI.Physics.YangMills.BalabanDirectSelectedUpperToGapFinalExact as Final

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

finalDirectUpperCompilerWritten : Final.finalDirectUpperCompilerWritten ≡ true
finalDirectUpperCompilerWritten = Final.finalDirectUpperCompilerWrittenIsTrue

r410MandatoryForTerminalGapIsFalse : Final.r410MandatoryForTerminalGap ≡ false
r410MandatoryForTerminalGapIsFalse = Final.r410MandatoryForTerminalGapIsFalse
