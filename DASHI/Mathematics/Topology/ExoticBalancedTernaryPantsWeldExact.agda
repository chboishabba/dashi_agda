module DASHI.Mathematics.Topology.ExoticBalancedTernaryPantsWeldExact where

------------------------------------------------------------------------
-- EXISTING OWNER WELD: BALANCED TERNARY / SSP369 / TWO PANTS
--
-- Original existing theorem carriers (not duplicated):
--   DASHI.Algebra.Trit: neg/zer/pos, sign involution
--   DASHI.Codec.BalancedTritBitFibre: zero vs signed support/sign
--   DASHI.Geometry.SSP369Ultrametric: ternary finite addresses
--   DASHI.Topology.TernaryCylinderPantsGeometryExact:
--     appendDigit / the already-composed two-pants 1 -> 3 channels
--   DASHI.Topology.TernaryPantsFrontierExact:
--     exact address/path equivalence + append naturality
--
-- Mapping is a CHOSEN encoding, not a theorem of numerology:
--     digit3 ↔ neg, digit6 ↔ zer, digit9 ↔ pos.
-- Its negation reflects 3↔9 while FIXING digit6.
-- It is NOT the order-three C3 cycle (3→6→9→3).
-- A 1→3 genus-zero branching cobordism has FOUR boundary circles,
-- hence is made from TWO ordinary three-boundary pairs of pants.
-- This module proves the indexing and compatibility, NOT a 2D
-- surface realisation or a probability-measure equality.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Vec using (Vec) renaming ([] to vnil; _∷_ to _vcons_)

import DASHI.Algebra.Trit as Trit
import DASHI.Foundations.BalancedTernaryStageSymmetryExact as Stage
import DASHI.Foundations.BalancedTernaryUltrametricExact as Ultra
import DASHI.Codec.BalancedTritBitFibre as Fibre
import DASHI.Geometry.SSP369Ultrametric as U369
import DASHI.Topology.TernaryCylinderPantsGeometryExact as Junction
import DASHI.Topology.TernaryPantsFrontierExact as Frontier

balancedOf369 : U369.Digit369 → Trit.Trit
balancedOf369 U369.digit3 = Trit.neg
balancedOf369 U369.digit6 = Trit.zer
balancedOf369 U369.digit9 = Trit.pos

digitOfBalanced : Trit.Trit → U369.Digit369
digitOfBalanced Trit.neg = U369.digit3
digitOfBalanced Trit.zer = U369.digit6
digitOfBalanced Trit.pos = U369.digit9

balancedDigitRoundTrip :
  (d : U369.Digit369) → digitOfBalanced (balancedOf369 d) ≡ d
balancedDigitRoundTrip U369.digit3 = refl
balancedDigitRoundTrip U369.digit6 = refl
balancedDigitRoundTrip U369.digit9 = refl

balancedTritRoundTrip :
  (t : Trit.Trit) → balancedOf369 (digitOfBalanced t) ≡ t
balancedTritRoundTrip Trit.neg = refl
balancedTritRoundTrip Trit.zer = refl
balancedTritRoundTrip Trit.pos = refl

reflect369 : U369.Digit369 → U369.Digit369
reflect369 U369.digit3 = U369.digit9
reflect369 U369.digit6 = U369.digit6
reflect369 U369.digit9 = U369.digit3

reflect369Involutive :
  (d : U369.Digit369) → reflect369 (reflect369 d) ≡ d
reflect369Involutive U369.digit3 = refl
reflect369Involutive U369.digit6 = refl
reflect369Involutive U369.digit9 = refl

reflectionIsBalancedSignInvolution :
  (d : U369.Digit369) →
  balancedOf369 (reflect369 d) ≡ Trit.inv (balancedOf369 d)
reflectionIsBalancedSignInvolution U369.digit3 = refl
reflectionIsBalancedSignInvolution U369.digit6 = refl
reflectionIsBalancedSignInvolution U369.digit9 = refl

-- Consume the EXISTING support/sign fibre, including the distinguished
-- zero fibre; do not pretend one ordinary binary sign represents zero.
slotToSignedFibre : U369.Digit369 → Fibre.TritFibre
slotToSignedFibre d = Fibre.encodeFibre (balancedOf369 d)

zeroSlotIsGenuineZeroFibre :
  slotToSignedFibre U369.digit6 ≡ Fibre.zeroFibre
zeroSlotIsGenuineZeroFibre = refl

negativeSlotIsSignedNegative :
  slotToSignedFibre U369.digit3 ≡
  Fibre.signedFibre Fibre.negativeSign
negativeSlotIsSignedNegative = refl

positiveSlotIsSignedPositive :
  slotToSignedFibre U369.digit9 ≡
  Fibre.signedFibre Fibre.positiveSign
positiveSlotIsSignedPositive = refl

balancedPathTo369 :
  ∀ {n : Nat} → Vec Trit.Trit n → U369.Address n
balancedPathTo369 vnil = vnil
balancedPathTo369 (head vcons tail) =
  digitOfBalanced head vcons balancedPathTo369 tail

address369ToBalanced :
  ∀ {n : Nat} → U369.Address n → Vec Trit.Trit n
address369ToBalanced vnil = vnil
address369ToBalanced (head vcons tail) =
  balancedOf369 head vcons address369ToBalanced tail

addressBalancedRoundTrip :
  ∀ {n : Nat} (path : U369.Address n) →
  balancedPathTo369 (address369ToBalanced path) ≡ path
addressBalancedRoundTrip vnil = refl
addressBalancedRoundTrip (head vcons tail)
  rewrite balancedDigitRoundTrip head
        | addressBalancedRoundTrip tail = refl

balancedAddressRoundTrip :
  ∀ {n : Nat} (path : Vec Trit.Trit n) →
  address369ToBalanced (balancedPathTo369 path) ≡ path
balancedAddressRoundTrip vnil = refl
balancedAddressRoundTrip (head vcons tail)
  rewrite balancedTritRoundTrip head
        | balancedAddressRoundTrip tail = refl

appendBalanced :
  ∀ {n : Nat} → Vec Trit.Trit n → Trit.Trit →
  Vec Trit.Trit (suc n)
appendBalanced vnil digit = digit vcons vnil
appendBalanced (head vcons tail) digit =
  head vcons appendBalanced tail digit

balancedAppendNaturality :
  ∀ {n : Nat} (prefix : Vec Trit.Trit n) (digit : Trit.Trit) →
  balancedPathTo369 (appendBalanced prefix digit) ≡
  Junction.appendDigit (balancedPathTo369 prefix)
                      (digitOfBalanced digit)
balancedAppendNaturality vnil digit = refl
balancedAppendNaturality (head vcons tail) digit
  rewrite balancedAppendNaturality tail digit = refl

-- THE EXISTING PANTS APPEND THEOREM does the final work, not a new
-- bespoke ternary surface/slot equivalence.
balancedPantsAppendNaturality :
  ∀ {n : Nat} (prefix : Vec Trit.Trit n) (digit : Trit.Trit) →
  Frontier.addressToPantsPath
    (balancedPathTo369 (appendBalanced prefix digit))
  ≡ Frontier.appendSlot
       (Frontier.addressToPantsPath (balancedPathTo369 prefix))
       (Junction.slotOfDigit (digitOfBalanced digit))
balancedPantsAppendNaturality prefix digit
  rewrite balancedAppendNaturality prefix digit =
  Frontier.addressToPantsPathAppend
    (balancedPathTo369 prefix) (digitOfBalanced digit)

-- This is a branch-slot *bijection* on arbitrary finite-depth words.
-- The main geometric payment is done in the separately tested finite
-- PL two-pants surface construction, not assumed by this theorem.

------------------------------------------------------------------------
-- EXACT PREFIX-ULTRAMETRIC DONOR FROM BALANCED TERNARY
--
-- This is deliberately a bridge into the ORIGINAL prefix-agreement
-- type, rather than a second standalone "ternary metric".
------------------------------------------------------------------------

stageBalancedDigitOf369 :
  U369.Digit369 → Stage.BalancedDigit
stageBalancedDigitOf369 U369.digit3 = Stage.neg
stageBalancedDigitOf369 U369.digit6 = Stage.zeroDigit
stageBalancedDigitOf369 U369.digit9 = Stage.pos

stageAddressList :
  ∀ {n : Nat} → U369.Address n → List Stage.BalancedDigit
stageAddressList vnil = []
stageAddressList (head vcons tail) =
  stageBalancedDigitOf369 head ∷ stageAddressList tail

sspPrefixPreservesBalancedUltrametric :
  ∀ {d k : Nat} {a b : U369.Address d} →
  U369.PrefixMatch k a b →
  Ultra.PrefixAgreement k (stageAddressList a) (stageAddressList b)
sspPrefixPreservesBalancedUltrametric U369.prefix-zero =
  Ultra.agreeZero
sspPrefixPreservesBalancedUltrametric (U369.prefix-cons U369.digit3 p) =
  Ultra.agreeNeg (sspPrefixPreservesBalancedUltrametric p)
sspPrefixPreservesBalancedUltrametric (U369.prefix-cons U369.digit6 p) =
  Ultra.agreeOpen (sspPrefixPreservesBalancedUltrametric p)
sspPrefixPreservesBalancedUltrametric (U369.prefix-cons U369.digit9 p) =
  Ultra.agreePos (sspPrefixPreservesBalancedUltrametric p)

-- The standard prefix radix 3 is source-owned by Ultra:
-- `Ultra.prefixScaleDenominator n = 3 ^ n`, no new metric.
-- This does NOT identify the resulting 3-adic group structure
-- with binary 2-adic group structure under the variable-length code.
