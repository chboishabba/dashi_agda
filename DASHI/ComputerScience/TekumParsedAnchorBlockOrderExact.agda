module DASHI.ComputerScience.TekumParsedAnchorBlockOrderExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties as NatP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.ComputerScience.TekumParsedAnchorCodeExact as Code
import DASHI.ComputerScience.TekumRegimeChainExact as Chain
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source

------------------------------------------------------------------------
-- FULL PARSED-ANCHOR CODE ORDER -> REGIME/PAYLOAD BLOCK ORDER
------------------------------------------------------------------------

data ParsedBlockOrder
    {extra r s payload₁ payload₂}
    (left : Source.ParsedPayload extra r payload₁)
    (right : Source.ParsedPayload extra s payload₂) : Set where
  earlierRegime :
    Chain.regimeIndex r < Chain.regimeIndex s →
    ParsedBlockOrder left right
  sameRegimeSmallerPayload :
    r ≡ s →
    Code.payloadCode left < Code.payloadCode right →
    ParsedBlockOrder left right

nextBlockUpper :
  ∀ {u p r : Nat} →
  u < p →
  u + p * r < p * suc r
nextBlockUpper {u} {p} {r} u<p =
  subst
    (λ z → u + p * r < z)
    blockSucc
    (NatP.+-monoʳ-< (p * r) u<p)
  where
  blockSucc : p + p * r ≡ p * suc r
  blockSucc =
    solve 2
      (λ x y → x :+ (x :* y) := x :* (con 1 :+ y))
      refl p r

laterRegimeForcesReverseCodeOrder :
  ∀ {extra r s payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra s payload₂) →
  Chain.regimeIndex s < Chain.regimeIndex r →
  Code.parsedAnchorCode right < Code.parsedAnchorCode left
laterRegimeForcesReverseCodeOrder {extra} {r} {s} left right s<r =
  subst
    (λ leftCode → Code.parsedAnchorCode right < leftCode)
    (sym (Code.parsedAnchorCodeFormula left))
    (subst
      (λ rightCode →
        rightCode
        < Code.payloadCode left + BT.pow3 (5 + extra) * Code.regimeCode r)
      (sym (Code.parsedAnchorCodeFormula right))
      normalized)
  where
  p = BT.pow3 (5 + extra)

  regimeStep : suc (Code.regimeCode s) ≤ Code.regimeCode r
  regimeStep
    rewrite Code.regimeCodeIsSixPlusIndex s
          | Code.regimeCodeIsSixPlusIndex r =
    subst
      (λ z → z ≤ 6 + Chain.regimeIndex r)
      (solve 1
        (λ j → con 1 :+ (con 6 :+ j) := con 6 :+ (con 1 :+ j))
        refl (Chain.regimeIndex s))
      (NatP.+-monoˡ-≤ 6 s<r)

  scaledRegimeStep :
    p * suc (Code.regimeCode s) ≤ p * Code.regimeCode r
  scaledRegimeStep = NatP.*-mono-≤ NatP.≤-refl regimeStep

  rightBelowLeftBase :
    Code.payloadCode right + p * Code.regimeCode s
    < p * Code.regimeCode r
  rightBelowLeftBase =
    NatP.<-≤-trans
      (nextBlockUpper (Code.payloadCodeBound right))
      scaledRegimeStep

  leftBaseBelowLeft :
    p * Code.regimeCode r
    ≤ Code.payloadCode left + p * Code.regimeCode r
  leftBaseBelowLeft =
    NatP.m≤n+m (p * Code.regimeCode r) (Code.payloadCode left)

  normalized :
    Code.payloadCode right + p * Code.regimeCode s
    < Code.payloadCode left + p * Code.regimeCode r
  normalized =
    NatP.<-≤-trans rightBelowLeftBase leftBaseBelowLeft

sameRegimeCodeOrderForcesPayloadOrder :
  ∀ {extra r s payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra s payload₂) →
  Chain.regimeIndex r ≡ Chain.regimeIndex s →
  Code.parsedAnchorCode left < Code.parsedAnchorCode right →
  Code.payloadCode left < Code.payloadCode right
sameRegimeCodeOrderForcesPayloadOrder {extra} {r} {s}
    left right indexEq codeLt =
  NatP.+-cancelʳ-<
    (Code.payloadCode left)
    (Code.payloadCode right)
    (BT.pow3 (5 + extra) * Code.regimeCode r)
    commonTailOrder
  where
  regimeEq : r ≡ s
  regimeEq = Chain.regimeIndexInjective indexEq

  commonTailOrder :
    Code.payloadCode left + BT.pow3 (5 + extra) * Code.regimeCode r
    < Code.payloadCode right + BT.pow3 (5 + extra) * Code.regimeCode r
  commonTailOrder
    rewrite regimeEq =
    subst
      (λ leftCode →
        leftCode
        < Code.payloadCode right + BT.pow3 (5 + extra) * Code.regimeCode s)
      (Code.parsedAnchorCodeFormula left)
      (subst
        (λ rightCode → Code.parsedAnchorCode left < rightCode)
        (Code.parsedAnchorCodeFormula right)
        codeLt)

parsedAnchorCodeStrictImpliesBlockOrder :
  ∀ {extra r s payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra s payload₂) →
  Code.parsedAnchorCode left < Code.parsedAnchorCode right →
  ParsedBlockOrder left right
parsedAnchorCodeStrictImpliesBlockOrder {r = r} {s = s} left right codeLt
  with NatP.<-cmp (Chain.regimeIndex r) (Chain.regimeIndex s)
... | tri< r<s _ _ = earlierRegime r<s
... | tri≈ _ r≡s _ =
  sameRegimeSmallerPayload
    (Chain.regimeIndexInjective r≡s)
    (sameRegimeCodeOrderForcesPayloadOrder left right r≡s codeLt)
... | tri> _ _ r>s =
  ⊥-elim
    (NatP.<-asym codeLt (laterRegimeForcesReverseCodeOrder left right r>s))
