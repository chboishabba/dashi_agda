module DASHI.Physics.Closure.NSTriadKNSelectedPacketNonzeroCutoffBridgeRegression where

open import Agda.Builtin.Bool using (true)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNSelectedPacketNonzeroCutoffBridgeExact as Subject

rejectZeroSelectorBridgeClosed :
  Subject.rejectZeroSelectorFullToNonzeroCutoffClosed ≡ true
rejectZeroSelectorBridgeClosed =
  Subject.rejectZeroSelectorFullToNonzeroCutoffClosedIsTrue

sameObjectCarrierPreserved :
  Subject.nonzeroCutoffBridgeIntroducesNoNewProductionScalar ≡ true
sameObjectCarrierPreserved =
  Subject.nonzeroCutoffBridgeIntroducesNoNewProductionScalarIsTrue
