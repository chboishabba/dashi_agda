module DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepBlocksFromLiteralRowsMaxCutTest where

open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNFixedOutputPhysicalDeepBlocksFromLiteralRowsMaxCutExact as Cut

sameObjectRemoved : Cut.b1B3LiveBlockSameObjectFieldsCompiledFromRows ≡ true
sameObjectRemoved = refl

analyticReceiptsRemain : Cut.b1B3RowsToAnalyticReceiptsClosedHere ≡ false
analyticReceiptsRemain = refl
