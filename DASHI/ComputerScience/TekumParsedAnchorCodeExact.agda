module DASHI.ComputerScience.TekumParsedAnchorCodeExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_,_)
import Data.List.Base as List
import Data.List.Properties as ListP
import Data.Vec.Base as Vec
import Data.Vec.Properties as VecP
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.ComputerScience.TekumFixedWidthBalancedArithmeticExact as Fixed
import DASHI.ComputerScience.TekumParsedAnchorListExact as AnchorList
import DASHI.ComputerScience.TekumRegimeChainExact as Chain
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumRegimeSuccessorExact as RegimeStep
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSourceWordRoundTripExact as RoundTrip

------------------------------------------------------------------------
-- RADIX-3 BLOCK CODE FOR SUCCESSFULLY PARSED ANCHORS
--
-- A parsed anchor is LST-first as
--
--   payload(5+extra trits) ++ regime(3 trits).
--
-- Hence its shifted base-three code is exactly
--
--   U + 3^(5+extra) * R,
--
-- where 0 <= U < 3^(5+extra). This is the block decomposition needed to
-- turn full anchor-code order into regime-first lexicographic order.
------------------------------------------------------------------------

listCode : List.List Trit.Trit → Nat
listCode List.[] = 0
listCode (t List.∷ ts) = Positional.digitNat t + 3 * listCode ts

listCodeToNatCode :
  ∀ {n} (word : Vec.Vec Trit.Trit n) →
  listCode (Vec.toList word) ≡ Positional.natCode word
listCodeToNatCode Vec.[] = refl
listCodeToNatCode (t Vec.∷ ts)
  rewrite listCodeToNatCode ts = refl

listCodeAppend :
  (left right : List.List Trit.Trit) →
  listCode (left List.++ right)
  ≡ listCode left + BT.pow3 (List.length left) * listCode right
listCodeAppend List.[] right = refl
listCodeAppend (t List.∷ ts) right
  rewrite listCodeAppend ts right =
  solve 3
    (λ d a b →
      d :+ (con 3 :* (a :+ b))
      := (d :+ (con 3 :* a)) :+ (con 3 :* b))
    refl
    (Positional.digitNat t)
    (listCode ts)
    (BT.pow3 (List.length ts) * listCode right)

payloadList :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload →
  List.List Trit.Trit
payloadList parsed =
  List.reverse (Vec.toList (RoundTrip.rejoinPayload parsed))

payloadCode :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → Nat
payloadCode parsed = listCode (payloadList parsed)

regimeCode : Regime.RegimeCode → Nat
regimeCode r = listCode (Vec.toList (RegimeStep.regimeLST r))

payloadLength :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  List.length (payloadList parsed) ≡ 5 + extra
payloadLength parsed =
  trans
    (ListP.length-reverse (Vec.toList (RoundTrip.rejoinPayload parsed)))
    (VecP.length-toList (RoundTrip.rejoinPayload parsed))

payloadListIsReversedVec :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  payloadList parsed
  ≡ Vec.toList (Vec.reverse (RoundTrip.rejoinPayload parsed))
payloadListIsReversedVec parsed =
  sym (VecP.toList-reverse (RoundTrip.rejoinPayload parsed))

payloadCodeBound :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  payloadCode parsed < BT.pow3 (5 + extra)
payloadCodeBound {extra} parsed =
  subst
    (λ k → k < BT.pow3 (5 + extra))
    (sym payloadCodeAsNatCode)
    (Rank.natCodeStrictBound (Vec.reverse (RoundTrip.rejoinPayload parsed)))
  where
  payloadCodeAsNatCode :
    payloadCode parsed
    ≡ Positional.natCode (Vec.reverse (RoundTrip.rejoinPayload parsed))
  payloadCodeAsNatCode =
    trans
      (cong listCode (payloadListIsReversedVec parsed))
      (listCodeToNatCode (Vec.reverse (RoundTrip.rejoinPayload parsed)))

parsedAnchorListAsPayloadRegime :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  AnchorList.parsedAnchorList parsed
  ≡ payloadList parsed List.++ Vec.toList (RegimeStep.regimeLST r)
parsedAnchorListAsPayloadRegime {r = r} parsed =
  cong
    (λ xs → xs List.++ Vec.toList (RegimeStep.regimeLST r))
    (sym (AnchorList.rejoinPayloadReverseList parsed))

parsedAnchorCode :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → Nat
parsedAnchorCode parsed = listCode (AnchorList.parsedAnchorList parsed)

parsedAnchorCodeFormula :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  parsedAnchorCode parsed
  ≡ payloadCode parsed + BT.pow3 (5 + extra) * regimeCode r
parsedAnchorCodeFormula {extra} {r} parsed =
  trans
    (cong listCode (parsedAnchorListAsPayloadRegime parsed))
    (trans
      (listCodeAppend
        (payloadList parsed)
        (Vec.toList (RegimeStep.regimeLST r)))
      (cong
        (λ n → payloadCode parsed + BT.pow3 n * regimeCode r)
        (payloadLength parsed)))

successfulParseNatCode :
  ∀ {extra r payload parsed}
  (word : Vec.Vec Trit.Trit (8 + extra)) →
  Source.parseOrdinaryAnchor word ≡ just (r , payload , parsed) →
  Positional.natCode (Fixed.concreteAnchor word) ≡ parsedAnchorCode parsed
successfulParseNatCode word parseEq =
  trans
    (sym (listCodeToNatCode (Fixed.concreteAnchor word)))
    (cong listCode (AnchorList.successfulParseAnchorList word parseEq))

regimeCodeIsSixPlusIndex :
  (r : Regime.RegimeCode) →
  regimeCode r ≡ 6 + Chain.regimeIndex r
regimeCodeIsSixPlusIndex Regime.rm7 = refl
regimeCodeIsSixPlusIndex Regime.rm6 = refl
regimeCodeIsSixPlusIndex Regime.rm5 = refl
regimeCodeIsSixPlusIndex Regime.rm4 = refl
regimeCodeIsSixPlusIndex Regime.rm3 = refl
regimeCodeIsSixPlusIndex Regime.rm2 = refl
regimeCodeIsSixPlusIndex Regime.rm1 = refl
regimeCodeIsSixPlusIndex Regime.r0 = refl
regimeCodeIsSixPlusIndex Regime.rp1 = refl
regimeCodeIsSixPlusIndex Regime.rp2 = refl
regimeCodeIsSixPlusIndex Regime.rp3 = refl
regimeCodeIsSixPlusIndex Regime.rp4 = refl
regimeCodeIsSixPlusIndex Regime.rp5 = refl
regimeCodeIsSixPlusIndex Regime.rp6 = refl
regimeCodeIsSixPlusIndex Regime.rp7 = refl
