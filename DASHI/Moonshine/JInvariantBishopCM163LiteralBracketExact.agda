module DASHI.Moonshine.JInvariantBishopCM163LiteralBracketExact where

-- Source-written. Evaluate the signed Rankin-Cohen bracket and its
-- differentiated coefficient identity on the original selected disk.
open import Agda.Builtin.Nat using (Nat)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_; _⋆)
import RealProperties as P
import DASHI.Moonshine.JInvariantBishopFormalSeriesRingExact as G
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as T
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
import DASHI.Moonshine.JInvariantBishopLiteralRamanujanExact as L
import DASHI.Moonshine.JInvariantBishopCM163LiteralRealSliceEvaluationExact as S
import DASHI.Moonshine.JInvariantBishopCM163LiteralNormBudgetExact as B
import DASHI.Moonshine.JInvariantBishopCM163FormalEvaluationConsumerExact as V
import DASHI.Moonshine.JInvariantBishopWeightedCauchyEvaluationExact as W
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
open G
open F using (δ)

-- An evaluated expression retains the original formal stream and its
-- absolute-convergence witness. No new analytic convergence axiom.
record Readout : Set where
  constructor readout
  field
    series : Series
    value : ℝ
    absolute : V.Abs series
    evaluation : V.Eval series value
open Readout

x y x1 y1 x2 y2 : Readout
x = readout U.X J.X S.xAbs S.xEval
y = readout U.Y J.Y S.yAbs S.yEval
x1 = readout (U.D 1 U.X) (S.xJet 0) (S.xJetAbs 0) (S.xJetEval 0)
y1 = readout (U.D 1 U.Y) (S.yJet 0) (S.yJetAbs 0) (S.yJetEval 0)
x2 = readout (U.D 2 U.X) (S.xJet 1) (S.xJetAbs 1) (S.xJetEval 1)
y2 = readout (U.D 2 U.Y) (S.yJet 1) (S.yJetAbs 1) (S.yJetEval 1)

infixl 6 _⊞_ _⊟_
infixl 7 _⊠_
_⊠_ : Readout → Readout → Readout
a ⊠ b = readout (series a ⊗s series b) (value a * value b)
  (W.weightedProductAbsolute V.q (series a) (series b) (absolute a) (absolute b))
  (W.weightedProductLimit V.q (series a) (series b) (value a) (value b)
    (absolute a) (absolute b) (evaluation a) (evaluation b))

_⊞_ : Readout → Readout → Readout
a ⊞ b = readout (series a ⊕s series b) (value a + value b)
  (B.addAbs (series a) (series b) (absolute a) (absolute b))
  (S.transport _ _ (value a + value b)
    (λ n → P.*-distribˡ-+ (R.pow V.q n) (series a n) (series b n))
    (proj₂ (B.sumConv (W.weighted V.q (series a)) (W.weighted V.q (series b))
      (value a , evaluation a) (value b , evaluation b))))

negative : Readout → Readout
negative a = readout (G.neg (series a)) (R.- value a)
  (B.witness (B.negBound (B.bounded (absolute a) P.≤-refl)))
  (S.transport _ _ (R.- value a)
    (λ n → let open P.ℝ-Solver in solve 2
      (λ q a → q ⊗ (⊝ a) ⊜ ⊝ (q ⊗ a)) P.≃-refl
      (R.pow V.q n) (series a n))
    (S.negLimit (W.weighted V.q (series a)) (value a) (evaluation a)))

_⊟_ : Readout → Readout → Readout
a ⊟ b = a ⊞ negative b

twice thrice : Readout → Readout
twice a = a ⊞ a
thrice a = a ⊞ a ⊞ a

bracket disc : Readout
bracket = thrice (y ⊠ x1) ⊟ twice (x ⊠ y1)
disc = x ⊠ x ⊠ x ⊟ y ⊠ y

-- Ramanujan supplies the actual all-index bracket identity.
formalBracket : series bracket ≈s series disc
formalBracket =
  let a = U.Y ⊗s δ U.X
      b = U.X ⊗s δ U.Y
      hx = transS L.ramanujanX (G.scaleIsProduct (+ 1 / 3) ((T.E ⊗s U.X) ⊖s U.Y))
      hy = transS L.ramanujanY (G.scaleIsProduct (+ 1 / 2) ((T.E ⊗s U.Y) ⊖s (U.X ⊗s U.X)))
      ha = mulCong reflS hx
      hb = mulCong reflS hy
      open G.Solver
  in transS (subCong (addCong (addCong ha ha) ha) (addCong hb hb))
    (solve 3 (λ e x y →
      (y ⊗ (Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y)) ⊕
       y ⊗ (Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y)) ⊕
       y ⊗ (Κ (+ 1 / 3) ⊗ (e ⊗ x ⊖ y))) ⊖
      (x ⊗ (Κ (+ 1 / 2) ⊗ (e ⊗ y ⊖ x ⊗ x)) ⊕
       x ⊗ (Κ (+ 1 / 2) ⊗ (e ⊗ y ⊖ x ⊗ x)))
      ⊜ x ⊗ x ⊗ x ⊖ y ⊗ y) reflS T.E U.X U.Y)

sameValue : (a b : Readout) → series a ≈s series b → value a ≃ value b
sameValue a b h = V.sameEval (series a) (series b) (value a) (value b)
  h (evaluation a) (evaluation b)

bracketValue : value bracket ≃ value disc
bracketValue = sameValue bracket disc formalBracket

actualBracket : J.Bracket
actualBracket =
  let open P.ℝ-Solver in
  P.≃-trans
    (solve 4 (λ x y a b →
      y ⊗ (Κ (+ 3 / 1) ⊗ a) ⊖ x ⊗ (Κ (+ 2 / 1) ⊗ b)
      ⊜ (y ⊗ a ⊕ y ⊗ a ⊕ y ⊗ a) ⊖ (x ⊗ b ⊕ x ⊗ b))
      P.≃-refl J.X J.Y (value x1) (value y1))
    bracketValue

-- Differentiate the same identity, using the original Leibniz owner.
dPair : (a b da db : Readout) → δ (series a) ≈s series da →
  δ (series b) ≈s series db →
  δ (series (a ⊠ b)) ≈s series (da ⊠ b ⊞ a ⊠ db)
dPair a b da db ha hb = transS (F.dMul (series a) (series b))
  (addCong (mulCong ha reflS) (mulCong reflS hb))

dTriple : (a da : Readout) → δ (series a) ≈s series da →
  δ (series (thrice a)) ≈s series (thrice da)
dTriple a da h = transS (F.dAdd (series (a ⊞ a)) (series a))
  (addCong (transS (F.dAdd (series a) (series a)) (addCong h h)) h)

dDouble : (a da : Readout) → δ (series a) ≈s series da →
  δ (series (twice a)) ≈s series (twice da)
dDouble a da h = transS (F.dAdd (series a) (series a)) (addCong h h)

dbracket ddisc : Readout
dbracket = thrice (y1 ⊠ x1 ⊞ y ⊠ x2) ⊟ twice (x1 ⊠ y1 ⊞ x ⊠ y2)
ddisc = (x1 ⊠ x ⊞ x ⊠ x1) ⊠ x ⊞ (x ⊠ x) ⊠ x1 ⊟ (y1 ⊠ y ⊞ y ⊠ y1)

dBracketRead : δ (series bracket) ≈s series dbracket
dBracketRead = transS (F.dSub (series (thrice (y ⊠ x1))) (series (twice (x ⊠ y1))))
  (subCong
    (dTriple (y ⊠ x1) (y1 ⊠ x1 ⊞ y ⊠ x2)
      (dPair y x1 y1 x2 reflS (F.dRepeat2 U.X)))
    (dDouble (x ⊠ y1) (x1 ⊠ y1 ⊞ x ⊠ y2)
      (dPair x y1 x1 y2 reflS (F.dRepeat2 U.Y))))

dDiscRead : δ (series disc) ≈s series ddisc
dDiscRead = transS (F.dSub (series (x ⊠ x ⊠ x)) (series (y ⊠ y)))
  (subCong
    (dPair (x ⊠ x) x (x1 ⊠ x ⊞ x ⊠ x1) x1
      (dPair x x x1 x1 reflS reflS) reflS)
    (dPair y y y1 y1 reflS reflS))

dBracketValue : value dbracket ≃ value ddisc
dBracketValue = sameValue dbracket ddisc
  (transS (symS dBracketRead) (transS (F.dCong formalBracket) dDiscRead))
