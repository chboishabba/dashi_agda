module DASHI.ComputerScience.InfotonP30FiniteAuditExact where

-- Walker/Infoton P30 *source-number audit*, not a formal proof of P30 or
-- physical energy savings.  Exact arithmetic and an explicit reuse seam for
-- the existing balanced-ternary formal codec; no new axioms or postulates.
-- Primary source: https://infoton.ai/infoton-p30 (PDF pp. 28-31).

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _+_; _*_)
open import DASHI.Algebra.Trit using (Trit)
import DASHI.Codec.BalancedTritBitFibre as Existing

p30HasNontrivialFactors : 30 ≡ 5 * 6
p30HasNontrivialFactors = refl

p30TwoDigitsHave900States : 30 * 30 ≡ 900
p30TwoDigitsHave900States = refl

p30UnitAlphabetTwoDigitsOnly64States : 8 * 8 ≡ 64
p30UnitAlphabetTwoDigitsOnly64States = refl

p30UnitAlphabetThreeDigits512States : 8 * (8 * 8) ≡ 512
p30UnitAlphabetThreeDigits512States = refl

byteAlphabetHas256States : 2 * (2 * (2 * (2 * (2 * (2 * (2 * 2)))))) ≡ 256
byteAlphabetHas256States = refl

p30FullRoundtripPackedExceedsUTF8By8 : 171 ≡ 163 + 8
p30FullRoundtripPackedExceedsUTF8By8 = refl

p30DirectWriteOnlyExceedsHuffmanPayloadBy13 : 116 ≡ 103 + 13
p30DirectWriteOnlyExceedsHuffmanPayloadBy13 = refl

reportedBaselineOperationsAre75TimesIngressPlus39 :
  12264 ≡ 75 * 163 + 39
reportedBaselineOperationsAre75TimesIngressPlus39 = refl

-- A bit toggle is a permutation; logical erasure is not injective.
-- This finite witness refutes treating every bit flip as bit erasure.
flip : Bool → Bool
flip true = false
flip false = true

flipInvolution : (b : Bool) → flip (flip b) ≡ b
flipInvolution true = refl
flipInvolution false = refl

clear : Bool → Bool
clear _ = false

clearIdentifiesDistinctInputs : clear false ≡ clear true
clearIdentifiesDistinctInputs = refl

-- Existing Agda owner is authoritative for the balanced-ternary codec.
-- This is a deliberate reuse; P30 is not declared equivalent to Trit.
reuseExistingTritRoundTrip :
  (t : Trit) → Existing.decodeFibre (Existing.encodeFibre t) ≡ t
reuseExistingTritRoundTrip = Existing.decode-encode
