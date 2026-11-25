module DASHI.Foundations.BishopChudnovskyPrefixSemanticsExact where

-- SOURCE-WRITTEN, UNCOMPILED.
-- Original raw prefix, signed product and rational sum. No new pi carrier.
-- The factorial identification is a separate source bridge; this module
-- proves intended rational prefix semantics from the actual merge edges.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥-elim)
import Data.Nat.Base as N
import Data.Nat.Properties as NP
open import Data.Integer using (ℤ; 0ℤ; 1ℤ; _+_; _*_)
import Data.Integer.Base as Z
open import Data.Integer.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import DASHI.Foundations.BishopChudnovskyRationalMidpointExact as CH
import DASHI.Foundations.BishopChudnovskyIndexedEdgeAlgebraExact as E
import DASHI.Foundations.BishopChudnovskyPositiveGapExact as G
import DASHI.Foundations.BishopChudnovskyWidthReflectionExact as W

frac : ℤ → (d : Nat) → N.NonZero d → Q.ℚᵘ
frac t d nz = Q._/_ t d {{nz}}

prodNZ : (d e : Nat) → N.NonZero d → N.NonZero e →
  N.NonZero (N._*_ d e)
prodNZ d e hd he = NP.m*n≢0 d e {{hd}} {{he}}

-- Denominator-cleared rational edge, including negative delta.
-- All denominators come from the original positive natural witnesses.
fracAddEdge : (t v : ℤ) (d e : Nat)
  (hd : N.NonZero d) (he : N.NonZero e) →
  frac (t * Z.+_ e + v) (N._*_ d e) (prodNZ d e hd he) Q.≃
  (frac t d hd Q.+ frac v (N._*_ d e) (prodNZ d e hd he))
fracAddEdge t v zero e hd he =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{hd}} refl)
fracAddEdge t v (suc d) zero hd he =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{he}} refl)
fracAddEdge t v (suc d) (suc e) hd he =
  Q.*≡*
    (solve 4 (λ t′ v′ d′ e′ →
      ((t′ :* e′) :+ v′) :* (d′ :* (d′ :* e′))
      := ((t′ :* (d′ :* e′)) :+ (v′ :* d′)) :* (d′ :* e′))
      refl t v (Z.+_ (suc d)) (Z.+_ (suc e)))

fracMulEdge : (p u : ℤ) (d e : Nat)
  (hd : N.NonZero d) (he : N.NonZero e) →
  frac (p * u) (N._*_ d e) (prodNZ d e hd he) Q.≃
  (frac p d hd Q.* frac u e he)
fracMulEdge p u zero e hd he =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{hd}} refl)
fracMulEdge p u (suc d) zero hd he =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{he}} refl)
fracMulEdge p u (suc d) (suc e) hd he = QP.≃-refl

fracWeight : (p a : ℤ) (d : Nat) (hd : N.NonZero d) →
  frac (p * a) d hd Q.≃
  (frac p d hd Q.* frac a 1 N.nonZero)
fracWeight p a zero hd =
  ⊥-elim (N.≢-nonZero⁻¹ zero {{hd}} refl)
fracWeight p a (suc d) hd =
  Q.*≡* (solve 3 (λ p′ a′ d′ →
    (p′ :* a′) :* (d′ :* con 1ℤ)
    := (p′ :* a′) :* d′) refl p a (Z.+_ (suc d)))

rawProduct rawSum : Nat → Q.ℚᵘ
rawProduct n = frac (E.P n) (G.qProduct n) (G.qProductNonZero n)
rawSum n = frac (E.T n) (G.qProduct n) (G.qProductNonZero n)

leafRatio : Nat → Q.ℚᵘ
leafRatio n = frac (CH.sourceP n) (G.qNat n) (G.qNatNonZero n)

weight : Nat → Q.ℚᵘ
weight n = frac (E.a n) 1 N.nonZero

rawProductStep : (n : Nat) →
  rawProduct (suc n) Q.≃ (rawProduct n Q.* leafRatio n)
rawProductStep n rewrite E.prefixPStep n =
  fracMulEdge (E.P n) (CH.sourceP n) (G.qProduct n) (G.qNat n)
    (G.qProductNonZero n) (G.qNatNonZero n)

rawSumStep : (n : Nat) →
  rawSum (suc n) Q.≃
  (rawSum n Q.+ (rawProduct (suc n) Q.* weight n))
rawSumStep n
  rewrite E.prefixTStep n | G.sourceQNatural n =
  QP.≃-trans
    (fracAddEdge (E.T n) (E.delta n) (G.qProduct n) (G.qNat n)
      (G.qProductNonZero n) (G.qNatNonZero n))
    (QP.+-cong QP.≃-refl
      (transWeight n))
  where
  transWeight : (j : Nat) →
    frac (E.delta j) (G.qProduct (suc j)) (G.qProductNonZero (suc j)) Q.≃
    (rawProduct (suc j) Q.* weight j)
  transWeight j rewrite E.prefixPStep j =
    fracWeight (E.P j * CH.sourceP j) (E.a j)
      (G.qProduct (suc j)) (G.qProductNonZero (suc j))

-- Independently defined rational stream with the literal signed leaves.
productPrefix : Nat → Q.ℚᵘ
productPrefix zero = Q.1ℚᵘ
productPrefix (suc n) = productPrefix n Q.* leafRatio n

sumPrefix : Nat → Q.ℚᵘ
sumPrefix zero = Q.0ℚᵘ
sumPrefix (suc n) = sumPrefix n Q.+ (productPrefix (suc n) Q.* weight n)

productSemantics : (n : Nat) → rawProduct n Q.≃ productPrefix n
productSemantics zero = QP.≃-refl
productSemantics (suc n) =
  QP.≃-trans (rawProductStep n)
    (QP.*-cong (productSemantics n) QP.≃-refl)

prefixSemantics : (n : Nat) → rawSum n Q.≃ sumPrefix n
prefixSemantics zero = QP.≃-refl
prefixSemantics (suc n) =
  QP.≃-trans (rawSumStep n)
    (QP.+-cong (prefixSemantics n)
      (QP.*-cong (productSemantics (suc n)) QP.≃-refl))

-- Original positiveView agrees with the same raw rational prefix.
-- Its actual numerator/denominator equalities are supplied by W.sourceView.
viewFraction : (v : CH.PositiveSum) → Q.ℚᵘ
viewFraction v = frac (Z.+_ (CH.num v)) (CH.den v) N.nonZero

literalView : (n : Nat) (v : W.View n) →
  rawSum (suc n) Q.≃ viewFraction (W.value v)
literalView n v rewrite W.numEq v | sym (W.sourceDen n v) = QP.≃-refl

literalPositivePrefix : (n : Nat) →
  viewFraction (W.value (W.sourceView n)) Q.≃ sumPrefix (suc n)
literalPositivePrefix n =
  QP.≃-trans (QP.≃-sym (literalView n (W.sourceView n)))
    (prefixSemantics (suc n))

-- No finite test or cross-prover carrier identification used here.
-- Remaining F1: identify productPrefix with the original factorial terms
-- on this carrier (or prove sound rational source reflection), then
-- bind the actual analytic limit and original rational endpoint.
