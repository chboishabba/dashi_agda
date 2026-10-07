module DASHI.ComputerScience.TekumParsedPayloadOrderExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; suc; _+_; _*_)
open import Data.Empty using (⊥-elim)
open import Data.Integer.Base as ℤ using (+_; -_; _+_; _<_ ; +<+)
import Data.Integer.Properties as ℤP
import Data.Nat.Properties as NatP
import Data.Vec.Properties as VecP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using () renaming
  ( solve to solveℤ
  ; _:+_ to _ℤ+_
  ; con to conℤ
  ; _:=_ to _ℤ=_
  )
open import Relation.Binary.Definitions using (tri<; tri≈; tri>)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym; trans)

import DASHI.Algebra.BalancedTernaryIntegerExact as BT
import DASHI.Algebra.BalancedTernaryPositionalInjectiveExact as Positional
import DASHI.Algebra.BalancedTernaryRankReconstructionExact as Rank
import DASHI.ComputerScience.TekumExactTriadicSemanticsExact as Exact
import DASHI.ComputerScience.TekumFractionOrderExact as FractionOrder
import DASHI.ComputerScience.TekumMonotoneMagnitudeExact as Monotone
import DASHI.ComputerScience.TekumOrdinaryFactorizationExact as Factor
import DASHI.ComputerScience.TekumParsedAnchorCodeExact as Code
import DASHI.ComputerScience.TekumParsedBandMembershipExact as Parsed
import DASHI.ComputerScience.TekumRegimeExponentExact as Regime
import DASHI.ComputerScience.TekumSignificandRangeExact as Sig
import DASHI.ComputerScience.TekumSourceWordDecodeExact as Source
import DASHI.ComputerScience.TekumSourceWordRoundTripExact as RoundTrip
import DASHI.ComputerScience.TekumParsedAnchorListExact as AnchorList

------------------------------------------------------------------------
-- CENTERED INTEGER ORDER FROM SHIFTED BASE-THREE CODE ORDER
------------------------------------------------------------------------

integerFromNatCode :
  ∀ {n} (word : Data.Vec.Base.Vec DASHI.Algebra.Trit.Trit n) →
  BT.toInteger (BT.eval word)
  ≡ (+ (Positional.natCode word)) ℤ.+ (ℤ.- (+ (Positional.center n)))
integerFromNatCode {n} word
  rewrite Positional.natCodeShift word =
  solveℤ 2
    (λ z c → z ℤ= (z ℤ+ c) ℤ+ (ℤ.- c))
    refl
    (BT.toInteger (BT.eval word))
    (+ (Positional.center n))

integerStrictFromNatCodeStrict :
  ∀ {n} {left right : Data.Vec.Base.Vec DASHI.Algebra.Trit.Trit n} →
  Positional.natCode left < Positional.natCode right →
  BT.toInteger (BT.eval left) ℤ.< BT.toInteger (BT.eval right)
integerStrictFromNatCodeStrict {n} {left} {right} codeLt
  rewrite integerFromNatCode left | integerFromNatCode right =
  ℤP.+-monoʳ-<
    (ℤ.- (+ (Positional.center n)))
    (+<+ codeLt)

------------------------------------------------------------------------
-- PAYLOAD RADIX BLOCK: fraction is low, exponent is high.
------------------------------------------------------------------------

fractionFieldCode :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → Nat
fractionFieldCode parsed = Positional.natCode (Source.fractionLST parsed)

exponentFieldCode :
  ∀ {extra r payload} →
  Source.ParsedPayload extra r payload → Nat
exponentFieldCode parsed = Positional.natCode (Source.exponentLST parsed)

payloadCodeFormula :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  Code.payloadCode parsed
  ≡ fractionFieldCode parsed
    + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode parsed
payloadCodeFormula {extra} {r} parsed =
  trans
    (cong Code.listCode (AnchorList.rejoinPayloadReverseList parsed))
    (trans
      (Code.listCodeAppend
        (Data.Vec.Base.toList (Source.fractionLST parsed))
        (Data.Vec.Base.toList (Source.exponentLST parsed)))
      normalized)
  where
  normalized :
    Code.listCode (Data.Vec.Base.toList (Source.fractionLST parsed))
      + BT.pow3 (Data.List.Base.length (Data.Vec.Base.toList (Source.fractionLST parsed)))
          * Code.listCode (Data.Vec.Base.toList (Source.exponentLST parsed))
    ≡ fractionFieldCode parsed
      + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode parsed
  normalized
    rewrite Code.listCodeToNatCode (Source.fractionLST parsed)
          | Code.listCodeToNatCode (Source.exponentLST parsed)
          | VecP.length-toList (Source.fractionLST parsed) = refl

fractionFieldCodeBound :
  ∀ {extra r payload}
  (parsed : Source.ParsedPayload extra r payload) →
  fractionFieldCode parsed < BT.pow3 (Regime.fractionCount (8 + extra) r)
fractionFieldCodeBound parsed = Rank.natCodeStrictBound (Source.fractionLST parsed)

data SameRegimePayloadOrder
    {extra r payload₁ payload₂}
    (left : Source.ParsedPayload extra r payload₁)
    (right : Source.ParsedPayload extra r payload₂) : Set where
  earlierExponentField :
    exponentFieldCode left < exponentFieldCode right →
    SameRegimePayloadOrder left right
  sameExponentSmallerFraction :
    exponentFieldCode left ≡ exponentFieldCode right →
    fractionFieldCode left < fractionFieldCode right →
    SameRegimePayloadOrder left right

nextPayloadBlockUpper :
  ∀ {u p e : Nat} →
  u < p →
  u + p * e < p * suc e
nextPayloadBlockUpper {u} {p} {e} u<p =
  subst
    (λ z → u + p * e < z)
    blockSucc
    (NatP.+-monoʳ-< (p * e) u<p)
  where
  blockSucc : p + p * e ≡ p * suc e
  blockSucc =
    solve 2
      (λ x y → x :+ (x :* y) := x :* (con 1 :+ y))
      refl p e

laterExponentForcesReversePayloadOrder :
  ∀ {extra r payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra r payload₂) →
  exponentFieldCode right < exponentFieldCode left →
  Code.payloadCode right < Code.payloadCode left
laterExponentForcesReversePayloadOrder {extra} {r} left right expLt
  rewrite payloadCodeFormula right | payloadCodeFormula left = normalized
  where
  p = BT.pow3 (Regime.fractionCount (8 + extra) r)

  exponentStep : suc (exponentFieldCode right) ≤ exponentFieldCode left
  exponentStep = expLt

  scaledExponentStep :
    p * suc (exponentFieldCode right) ≤ p * exponentFieldCode left
  scaledExponentStep = NatP.*-mono-≤ NatP.≤-refl exponentStep

  rightBelowLeftBase :
    fractionFieldCode right + p * exponentFieldCode right
    < p * exponentFieldCode left
  rightBelowLeftBase =
    NatP.<-≤-trans
      (nextPayloadBlockUpper (fractionFieldCodeBound right))
      scaledExponentStep

  leftBaseBelowLeft :
    p * exponentFieldCode left
    ≤ fractionFieldCode left + p * exponentFieldCode left
  leftBaseBelowLeft =
    NatP.m≤n+m (p * exponentFieldCode left) (fractionFieldCode left)

  normalized :
    fractionFieldCode right + p * exponentFieldCode right
    < fractionFieldCode left + p * exponentFieldCode left
  normalized = NatP.<-≤-trans rightBelowLeftBase leftBaseBelowLeft

sameExponentPayloadOrderForcesFractionOrder :
  ∀ {extra r payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra r payload₂) →
  exponentFieldCode left ≡ exponentFieldCode right →
  Code.payloadCode left < Code.payloadCode right →
  fractionFieldCode left < fractionFieldCode right
sameExponentPayloadOrderForcesFractionOrder {extra} {r}
    left right exponentEq payloadLt =
  NatP.+-cancelʳ-<
    (fractionFieldCode left)
    (fractionFieldCode right)
    (BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode left)
    commonTailOrder
  where
  normalized :
    fractionFieldCode left
      + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode left
    < fractionFieldCode right
      + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode right
  normalized
    rewrite sym (payloadCodeFormula left)
          | sym (payloadCodeFormula right) = payloadLt

  commonTailOrder :
    fractionFieldCode left
      + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode left
    < fractionFieldCode right
      + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode left
  commonTailOrder =
    subst
      (λ code →
        fractionFieldCode left
          + BT.pow3 (Regime.fractionCount (8 + extra) r) * exponentFieldCode left
        < fractionFieldCode right
          + BT.pow3 (Regime.fractionCount (8 + extra) r) * code)
      (sym exponentEq)
      normalized

payloadCodeStrictImpliesSameRegimeOrder :
  ∀ {extra r payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra r payload₂) →
  Code.payloadCode left < Code.payloadCode right →
  SameRegimePayloadOrder left right
payloadCodeStrictImpliesSameRegimeOrder left right payloadLt
  with NatP.<-cmp (exponentFieldCode left) (exponentFieldCode right)
... | tri< left<right _ _ = earlierExponentField left<right
... | tri≈ _ left≡right _ =
  sameExponentSmallerFraction left≡right
    (sameExponentPayloadOrderForcesFractionOrder left right left≡right payloadLt)
... | tri> _ _ left>right =
  ⊥-elim
    (NatP.<-asym payloadLt
      (laterExponentForcesReversePayloadOrder left right left>right))

------------------------------------------------------------------------
-- NUMERIC COMPILER FOR THE TWO SAME-REGIME CASES
------------------------------------------------------------------------

sameRegimeExponentFieldStrict :
  ∀ {extra r payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra r payload₂) →
  exponentFieldCode left < exponentFieldCode right →
  Factor.sourceExponentInteger left ℤ.< Factor.sourceExponentInteger right
sameRegimeExponentFieldStrict {r = r} left right codeLt
  rewrite Source.exponentIntCodeInteger left
        | Source.exponentIntCodeInteger right =
  ℤP.+-monoˡ-<
    (Exact.intCodeToInteger (Regime.bias r))
    (integerStrictFromNatCodeStrict codeLt)

sameRegimeExponentFieldEqual :
  ∀ {extra r payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra r payload₂) →
  exponentFieldCode left ≡ exponentFieldCode right →
  Factor.sourceExponentInteger left ≡ Factor.sourceExponentInteger right
sameRegimeExponentFieldEqual {r = r} left right codeEq =
  cong
    (λ z → z ℤ.+ Exact.intCodeToInteger (Regime.bias r))
    (cong
      (λ word → BT.toInteger (BT.eval word))
      (Positional.natCodeInjective codeEq))
  |> transport
  where
  transport :
    (BT.toInteger (BT.eval (Source.exponentLST left))
      ℤ.+ Exact.intCodeToInteger (Regime.bias r)
     ≡
     BT.toInteger (BT.eval (Source.exponentLST right))
      ℤ.+ Exact.intCodeToInteger (Regime.bias r)) →
    Factor.sourceExponentInteger left ≡ Factor.sourceExponentInteger right
  transport eq
    rewrite Source.exponentIntCodeInteger left
          | Source.exponentIntCodeInteger right = eq

sameRegimePayloadOrderStrict :
  ∀ {extra r payload₁ payload₂}
  (left : Source.ParsedPayload extra r payload₁)
  (right : Source.ParsedPayload extra r payload₂) →
  SameRegimePayloadOrder left right →
  Parsed.parsedMagnitude left Data.Rational.Base.< Parsed.parsedMagnitude right
sameRegimePayloadOrderStrict left right (earlierExponentField exponentLt) =
  Monotone.exponentStrictForcesMagnitudeStrict left right
    (sameRegimeExponentFieldStrict left right exponentLt)
sameRegimePayloadOrderStrict left right
    (sameExponentSmallerFraction exponentEq fractionLt) =
  Monotone.sameExponentSignificandStrictForcesMagnitudeStrict
    left right
    (sameRegimeExponentFieldEqual left right exponentEq)
    (FractionOrder.significandIntegerStrict
      (integerStrictFromNatCodeStrict fractionLt))
