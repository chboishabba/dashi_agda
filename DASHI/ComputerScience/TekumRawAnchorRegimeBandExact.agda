module DASHI.ComputerScience.TekumRawAnchorRegimeBandExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Base using (just)
open import Data.Product.Base using (_×_; _,_)
import Data.List.Base as List
import Data.List.Properties as ListP
import Data.Nat.Properties as NatP
import Data.Vec.Base as Vec
import Data.Vec.Properties as VecP
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.Trit as Trit
import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.ComputerScience.TekumAnchorCodecExact as Anchor
import DASHI.ComputerScience.TekumParsedAnchorCodeExact as Code
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime

------------------------------------------------------------------------
-- RAW 3-TRIT HIGH BLOCK OF AN ANCHOR READ MSB FIRST
------------------------------------------------------------------------

payloadScale : Nat → Nat
payloadScale extra = BT.pow3 (5 + extra)

rawPayloadCode :
  ∀ {extra} → Vec.Vec Trit.Trit (5 + extra) → Nat
rawPayloadCode payload =
  Code.listCode (List.reverse (Vec.toList payload))

rawRegimeCode : Trit.Trit → Trit.Trit → Trit.Trit → Nat
rawRegimeCode a b c =
  Code.listCode (c List.∷ b List.∷ a List.∷ List.[])

rawAnchorCode :
  ∀ {extra} → Vec.Vec Trit.Trit (8 + extra) → Nat
rawAnchorCode anchorMSB =
  Code.listCode (List.reverse (Vec.toList anchorMSB))

rawPayloadCodeBound :
  ∀ {extra} (payload : Vec.Vec Trit.Trit (5 + extra)) →
  rawPayloadCode payload < payloadScale extra
rawPayloadCodeBound {extra} payload =
  subst
    (λ code → code < BT.pow3 (5 + extra))
    (sym codeEq)
    (Rank.natCodeStrictBound (Vec.reverse payload))
  where
  codeEq :
    rawPayloadCode payload ≡ Positional.natCode (Vec.reverse payload)
  codeEq =
    trans
      (cong Code.listCode (sym (VecP.toList-reverse payload)))
      (Code.listCodeToNatCode (Vec.reverse payload))

rawAnchorCodeFormula :
  ∀ {extra}
  (a b c : Trit.Trit)
  (payload : Vec.Vec Trit.Trit (5 + extra)) →
  rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
  ≡ rawPayloadCode payload
    + payloadScale extra * rawRegimeCode a b c
rawAnchorCodeFormula {extra} a b c payload =
  trans reverseShape
    (trans
      (Code.listCodeAppend
        (List.reverse (Vec.toList payload))
        (c List.∷ b List.∷ a List.∷ List.[]))
      normalizedLength)
  where
  prefix = a List.∷ b List.∷ c List.∷ List.[]

  prefixAppend :
    prefix List.++ Vec.toList payload
    ≡ Vec.toList (a Vec.∷ b Vec.∷ c Vec.∷ payload)
  prefixAppend = refl

  reverseShape :
    Code.listCode
      (List.reverse (Vec.toList (a Vec.∷ b Vec.∷ c Vec.∷ payload)))
    ≡ Code.listCode
        (List.reverse (Vec.toList payload)
          List.++ (c List.∷ b List.∷ a List.∷ List.[]))
  reverseShape =
    cong Code.listCode
      (trans
        (cong List.reverse (sym prefixAppend))
        (ListP.reverse-++ prefix (Vec.toList payload)))

  reversePayloadLength :
    List.length (List.reverse (Vec.toList payload)) ≡ 5 + extra
  reversePayloadLength =
    trans
      (ListP.length-reverse (Vec.toList payload))
      (VecP.length-toList payload)

  normalizedLength :
    rawPayloadCode payload
      + BT.pow3 (List.length (List.reverse (Vec.toList payload)))
          * rawRegimeCode a b c
    ≡ rawPayloadCode payload
      + payloadScale extra * rawRegimeCode a b c
  normalizedLength =
    cong
      (λ n → rawPayloadCode payload + BT.pow3 n * rawRegimeCode a b c)
      reversePayloadLength

------------------------------------------------------------------------
-- A THREE-TRIT CODE IN [6,21) IS EXACTLY ONE OF THE SOURCE REGIME ROWS.
------------------------------------------------------------------------

record LegalRegimePrefix (a b c : Trit.Trit) : Set where
  constructor legalRegimePrefix
  field
    regime : Regime.RegimeCode
    decode : Regime.decodeRegime (Anchor.regime3 a b c) ≡ just regime
open LegalRegimePrefix public

legalRegimeFromCodeBand :
  (a b c : Trit.Trit) →
  6 ≤ rawRegimeCode a b c →
  rawRegimeCode a b c < 21 →
  LegalRegimePrefix a b c
legalRegimeFromCodeBand Trit.neg Trit.neg Trit.neg () upper
legalRegimeFromCodeBand Trit.neg Trit.neg Trit.zer () upper
legalRegimeFromCodeBand Trit.neg Trit.neg Trit.pos () upper
legalRegimeFromCodeBand Trit.neg Trit.zer Trit.neg () upper
legalRegimeFromCodeBand Trit.neg Trit.zer Trit.zer () upper
legalRegimeFromCodeBand Trit.neg Trit.zer Trit.pos () upper
legalRegimeFromCodeBand Trit.neg Trit.pos Trit.neg lower upper = legalRegimePrefix Regime.rm7 refl
legalRegimeFromCodeBand Trit.neg Trit.pos Trit.zer lower upper = legalRegimePrefix Regime.rm6 refl
legalRegimeFromCodeBand Trit.neg Trit.pos Trit.pos lower upper = legalRegimePrefix Regime.rm5 refl
legalRegimeFromCodeBand Trit.zer Trit.neg Trit.neg lower upper = legalRegimePrefix Regime.rm4 refl
legalRegimeFromCodeBand Trit.zer Trit.neg Trit.zer lower upper = legalRegimePrefix Regime.rm3 refl
legalRegimeFromCodeBand Trit.zer Trit.neg Trit.pos lower upper = legalRegimePrefix Regime.rm2 refl
legalRegimeFromCodeBand Trit.zer Trit.zer Trit.neg lower upper = legalRegimePrefix Regime.rm1 refl
legalRegimeFromCodeBand Trit.zer Trit.zer Trit.zer lower upper = legalRegimePrefix Regime.r0 refl
legalRegimeFromCodeBand Trit.zer Trit.zer Trit.pos lower upper = legalRegimePrefix Regime.rp1 refl
legalRegimeFromCodeBand Trit.zer Trit.pos Trit.neg lower upper = legalRegimePrefix Regime.rp2 refl
legalRegimeFromCodeBand Trit.zer Trit.pos Trit.zer lower upper = legalRegimePrefix Regime.rp3 refl
legalRegimeFromCodeBand Trit.zer Trit.pos Trit.pos lower upper = legalRegimePrefix Regime.rp4 refl
legalRegimeFromCodeBand Trit.pos Trit.neg Trit.neg lower upper = legalRegimePrefix Regime.rp5 refl
legalRegimeFromCodeBand Trit.pos Trit.neg Trit.zer lower upper = legalRegimePrefix Regime.rp6 refl
legalRegimeFromCodeBand Trit.pos Trit.neg Trit.pos lower upper = legalRegimePrefix Regime.rp7 refl
legalRegimeFromCodeBand Trit.pos Trit.zer Trit.neg lower ()
legalRegimeFromCodeBand Trit.pos Trit.zer Trit.zer lower ()
legalRegimeFromCodeBand Trit.pos Trit.zer Trit.pos lower ()
legalRegimeFromCodeBand Trit.pos Trit.pos Trit.neg lower ()
legalRegimeFromCodeBand Trit.pos Trit.pos Trit.zer lower ()
legalRegimeFromCodeBand Trit.pos Trit.pos Trit.pos lower ()

------------------------------------------------------------------------
-- WHOLE-CODE BAND FORCES THE PREFIX BAND.
------------------------------------------------------------------------

blockUpper :
  ∀ {u p r : Nat} →
  u < p →
  u + p * r < p * suc r
blockUpper {u} {p} {r} u<p =
  subst
    (λ z → u + p * r < z)
    (NatP.*-suc p r)
    (NatP.+-monoʳ-< (p * r) u<p)

prefixBelowSixForcesWholeBelowSixBlocks :
  ∀ {extra a b c}
  (payload : Vec.Vec Trit.Trit (5 + extra)) →
  rawRegimeCode a b c < 6 →
  rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
    < 6 * payloadScale extra
prefixBelowSixForcesWholeBelowSixBlocks {extra} {a} {b} {c} payload regimeLt
  rewrite rawAnchorCodeFormula a b c payload
        | NatP.*-comm 6 (payloadScale extra) =
  NatP.<-≤-trans
    (blockUpper (rawPayloadCodeBound payload))
    (NatP.*-mono-≤ NatP.≤-refl regimeLt)

prefixAtLeastTwentyOneForcesWholeAtLeast :
  ∀ {extra a b c}
  (payload : Vec.Vec Trit.Trit (5 + extra)) →
  21 ≤ rawRegimeCode a b c →
  21 * payloadScale extra
    ≤ rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
prefixAtLeastTwentyOneForcesWholeAtLeast {extra} {a} {b} {c} payload regimeBound
  rewrite rawAnchorCodeFormula a b c payload
        | NatP.*-comm 21 (payloadScale extra) =
  NatP.≤-trans
    (NatP.*-mono-≤ NatP.≤-refl regimeBound)
    (NatP.m≤n+m
      (payloadScale extra * rawRegimeCode a b c)
      (rawPayloadCode payload))

wholeBandForcesRegimeBand :
  ∀ {extra}
  (a b c : Trit.Trit)
  (payload : Vec.Vec Trit.Trit (5 + extra)) →
  6 * payloadScale extra
    ≤ rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload) →
  rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
    < 21 * payloadScale extra →
  (6 ≤ rawRegimeCode a b c) × (rawRegimeCode a b c < 21)
wholeBandForcesRegimeBand {extra} a b c payload lower upper =
  lowerRegime , upperRegime
  where
  lowerRegime : 6 ≤ rawRegimeCode a b c
  lowerRegime with NatP.<-cmp (rawRegimeCode a b c) 6
  ... | tri< regimeLt _ _ =
    ⊥-elim
      (NatP.<-irrefl refl
        (NatP.≤-<-trans lower
          (prefixBelowSixForcesWholeBelowSixBlocks payload regimeLt)))
  ... | tri≈ _ regimeEq _ =
    subst (6 ≤_) (sym regimeEq) NatP.≤-refl
  ... | tri> _ _ regimeGt = NatP.<⇒≤ regimeGt

  upperRegime : rawRegimeCode a b c < 21
  upperRegime with NatP.<-cmp (rawRegimeCode a b c) 21
  ... | tri< regimeLt _ _ = regimeLt
  ... | tri≈ _ regimeEq _ =
    ⊥-elim
      (NatP.<-irrefl refl
        (NatP.≤-<-trans highWhole lowerUpper))
    where
    highBound : 21 ≤ rawRegimeCode a b c
    highBound = subst (21 ≤_) (sym regimeEq) NatP.≤-refl
    highWhole :
      21 * payloadScale extra
      ≤ rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
    highWhole = prefixAtLeastTwentyOneForcesWholeAtLeast payload highBound
    lowerUpper = upper
  ... | tri> _ _ regimeGt =
    ⊥-elim
      (NatP.<-irrefl refl
        (NatP.≤-<-trans
          (prefixAtLeastTwentyOneForcesWholeAtLeast payload (NatP.<⇒≤ regimeGt))
          upper))

anchorBandParsesRegime :
  ∀ {extra}
  (a b c : Trit.Trit)
  (payload : Vec.Vec Trit.Trit (5 + extra)) →
  6 * payloadScale extra
    ≤ rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload) →
  rawAnchorCode (a Vec.∷ b Vec.∷ c Vec.∷ payload)
    < 21 * payloadScale extra →
  LegalRegimePrefix a b c
anchorBandParsesRegime a b c payload lower upper
  with wholeBandForcesRegimeBand a b c payload lower upper
... | regimeLower , regimeUpper =
  legalRegimeFromCodeBand a b c regimeLower regimeUpper
