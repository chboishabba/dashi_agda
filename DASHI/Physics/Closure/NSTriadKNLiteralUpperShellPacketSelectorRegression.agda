module DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorRegression where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.Closure.NSTriadKNLiteralUpperShellPacketSelectorExact as Subject

upperShellSelectorConstructed :
  Subject.literalUpperShellSelectorConstructed ≡ true
upperShellSelectorConstructed =
  Subject.literalUpperShellSelectorConstructedIsTrue

upperShellSelectorRejectsZero :
  Subject.literalUpperShellSelectorRejectsZeroClosed ≡ true
upperShellSelectorRejectsZero =
  Subject.literalUpperShellSelectorRejectsZeroClosedIsTrue

selectedPairingPermutationInvariant :
  Subject.selectedProjectedPairingPermutationInvariantClosed ≡ true
selectedPairingPermutationInvariant =
  Subject.selectedProjectedPairingPermutationInvariantClosedIsTrue

upperShellR98TransportClosed :
  Subject.literalUpperShellSelectorR98TransportClosed ≡ true
upperShellR98TransportClosed =
  Subject.literalUpperShellSelectorR98TransportClosedIsTrue

structuralSuffixStillOpen :
  Subject.r104StructuralSuffixEqualsUpperShellSelectorClosed ≡ false
structuralSuffixStillOpen =
  Subject.r104StructuralSuffixEqualsUpperShellSelectorClosedIsFalse
