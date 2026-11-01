module DASHI.Physics.Closure.NSTriadKNR104StrictShellJumpTailRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNR104StrictShellJumpTailExact as Subject

strictJumpDropSuffixClosed :
  Subject.strictShellJumpCanonicalDropClosed ≡ true
strictJumpDropSuffixClosed = Subject.strictShellJumpCanonicalDropClosedIsTrue

localR104TailCanonicalSuffixClosed :
  Subject.localR104StructuralTailCanonicalSuffixClosed ≡ true
localR104TailCanonicalSuffixClosed =
  Subject.localR104StructuralTailCanonicalSuffixClosedIsTrue

globalR104LayerCakePhysicalStillOpen :
  Subject.globalR104LayerCakePhysicalPacketWeldClosed ≡ false
globalR104LayerCakePhysicalStillOpen =
  Subject.globalR104LayerCakePhysicalPacketWeldClosedIsFalse
