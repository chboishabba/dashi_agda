module DASHI.Moonshine.JInvariantBishopRamanujanNativeExact where

-- Source-written, no new premise: the three literal formal Ramanujan
-- equations from the actual signed divisor identities and original Cauchy rows.
open import Agda.Builtin.Nat using (Nat; zero; suc)
import Agda.Builtin.Nat as N
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.List.Base using (List; []; _∷_)
open import Data.Integer.Base using (ℤ; +_)
import Data.Integer.Base as Z
import Data.Integer.Properties as ZP
import Data.Nat.Properties as NP
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)
import Real as R
open R using (ℝ; _≃_; _+_; _*_; _-_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopFiniteCauchyRingWeldExact as Ring
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as Row
import DASHI.Mathematics.NumberTheory.FiniteDivisorSumExact as Div
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Mathematics.NumberTheory.FiniteWeightedReindexExact as W
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionSigmaFoldExact as V
import DASHI.Mathematics.NumberTheory.FiniteDivisorConvolutionRamanujanIntegerExact as A
import DASHI.Moonshine.JInvariantBishopRamanujanRowTransportExact as T
import DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact as U
import DASHI.Moonshine.JInvariantBishopHyperQDefectReductionExact as D
import DASHI.Moonshine.JInvariantBishopHyperQFactorizationWeldExact as F
open T using (emb; embEq; embAdd; embMul; embNeg; stream)
open U using (Series; X; Y; _⊗s_)
open D using (E)

sigmaOneFold : (xs : List Nat) →
  W.foldNat (λ d → d) xs ≡ W.foldNat (λ d → Pow.powNat d 1) xs
sigmaOneFold [] = refl
sigmaOneFold (d ∷ ds) =
  trans (cong (λ v → d N.+ v) (sigmaOneFold ds))
    (cong (λ v → v N.+ W.foldNat (λ d → Pow.powNat d 1) ds) (sym (NP.*-identityʳ d)))

sigmaOne : (n : Nat) → Div.sigma1 n ≡ Pow.sigmaPower 1 n
sigmaOne n = sigmaOneFold (Div.positiveDivisors n)

negativeProduct : (a b : Nat) →
  Z.- (+ (a N.* b)) ≡ (Z.- (+ a)) Z.* (+ b)
negativeProduct a b =
  trans (cong Z.-_ (ZP.pos-* a b))
    (trans (sym (ZP.-1*i≡-i ((+ a) Z.* (+ b))))
      (trans (sym (ZP.*-assoc (Z.- (+ 1)) (+ a) (+ b)))
        (cong (λ v → v Z.* (+ b)) (ZP.-1*i≡-i (+ a)))))

eRead : (n : Nat) → E n ≃ emb (stream (Z.- (+ 24)) 1 n)
eRead zero = P.≃-refl
eRead (suc n) =
  P.≃-trans (P.≃-symm (embNeg (+ (24 N.* Div.sigma1 (suc n)))))
    (embEq (trans (cong (λ v → Z.- (+ (24 N.* v))) (sigmaOne (suc n)))
      (negativeProduct 24 (Pow.sigmaPower 1 (suc n)))))

xRead : (n : Nat) → X n ≃ emb (stream (+ 240) 3 n)
xRead zero = P.≃-refl
xRead (suc n) = embEq (ZP.pos-* 240 (Pow.sigmaPower 3 (suc n)))

yRead : (n : Nat) → Y n ≃ emb (stream (Z.- (+ 504)) 5 n)
yRead zero = P.≃-refl
yRead (suc n) =
  P.≃-trans (P.≃-symm (embNeg (+ (504 N.* Pow.sigmaPower 5 (suc n)))))
    (embEq (negativeProduct 504 (Pow.sigmaPower 5 (suc n))))

s : Nat → Nat → ℝ
s k n = emb (V.sigma k n)

c : Nat → Nat → Nat → ℝ
c k l n = emb (V.conv k l n)

eValue : (n : Nat) → E (suc n) ≃ emb (Z.- (+ 24)) * s 1 (suc n)
eValue n = P.≃-trans (eRead (suc n)) (embMul _ _)

xValue : (n : Nat) → X (suc n) ≃ emb (+ 240) * s 3 (suc n)
xValue n = P.≃-trans (xRead (suc n)) (embMul _ _)

yValue : (n : Nat) → Y (suc n) ≃ emb (Z.- (+ 504)) * s 5 (suc n)
yValue n = P.≃-trans (yRead (suc n)) (embMul _ _)

literalRow : (f g : Series) (a b : ℤ) (k l : Nat) →
  (∀ n → f n ≃ emb (stream a k n)) →
  (∀ n → g n ≃ emb (stream b l n)) →
  (n : Nat) → (f ⊗s g) (suc n) ≃
    emb a * s k (suc n) + emb b * s l (suc n) + (emb a * emb b) * c k l (suc n)
literalRow f g a b k l hf hg n =
  P.≃-trans (Ring.rowCong f g (λ i → emb (stream a k i)) (λ i → emb (stream b l i)) hf hg (suc n))
    (T.rowProduct a b k l n)

ee = literalRow E E (Z.- (+ 24)) (Z.- (+ 24)) 1 1 eRead eRead
ex = literalRow E X (Z.- (+ 24)) (+ 240) 1 3 eRead xRead
ey = literalRow E Y (Z.- (+ 24)) (Z.- (+ 504)) 1 5 eRead yRead
xx = literalRow X X (+ 240) (+ 240) 3 3 xRead xRead

-- Small expression interpretation: reflect the *proved* integer equations
-- to reals using homomorphism, rather than treating integer equality as
-- a Bishop equality or asking a real solver to know divisor identities.
data Expr : Set where
  atom : ℤ → Expr
  add mul : Expr → Expr → Expr

zEval : Expr → ℤ
zEval (atom z) = z
zEval (add a b) = zEval a Z.+ zEval b
zEval (mul a b) = zEval a Z.* zEval b

rEval : Expr → ℝ
rEval (atom z) = emb z
rEval (add a b) = rEval a + rEval b
rEval (mul a b) = rEval a * rEval b

reflect : (e : Expr) → emb (zEval e) ≃ rEval e
reflect (atom z) = P.≃-refl
reflect (add a b) = P.≃-trans (embAdd (zEval a) (zEval b)) (P.+-cong (reflect a) (reflect b))
reflect (mul a b) = P.≃-trans (embMul (zEval a) (zEval b)) (P.*-cong (reflect a) (reflect b))

lift : (a b : Expr) → zEval a ≡ zEval b → rEval a ≃ rEval b
lift a b h = P.≃-trans (P.≃-symm (reflect a)) (P.≃-trans (embEq h) (reflect b))

K : Nat → Expr
K n = atom (+ n)

negK : Nat → Expr
negK n = atom (Z.- (+ n))

S C : Nat → Nat → Expr
S k n = atom (V.sigma k n)
C k n = atom (V.conv k k n)

mixed : Nat → Nat → Nat → Expr
mixed k l n = atom (V.conv k l n)

c11R : (n : Nat) →
  emb (+ 12) * c 1 1 (suc n) ≃
    emb (+ 5) * s 3 (suc n) + (emb (+ 1) + emb (Z.- (+ 6)) * NR.natReal (suc n)) * s 1 (suc n)
c11R n =
  let m = suc n in
  lift (mul (K 12) (mixed 1 1 m))
    (add (mul (K 5) (S 3 m)) (mul (add (K 1) (mul (negK 6) (K m))) (S 1 m))) (A.c11 n)

c13R : (n : Nat) →
  emb (+ 240) * c 1 3 (suc n) ≃
    emb (+ 21) * s 5 (suc n) + (emb (+ 10) + emb (Z.- (+ 30)) * NR.natReal (suc n)) * s 3 (suc n) +
      emb (Z.- (+ 1)) * s 1 (suc n)
c13R n =
  let m = suc n in
  lift (mul (K 240) (mixed 1 3 m))
    (add (add (mul (K 21) (S 5 m)) (mul (add (K 10) (mul (negK 30) (K m))) (S 3 m)))
      (mul (negK 1) (S 1 m))) (A.c13 n)

c15R : (n : Nat) →
  emb (+ 5040) * c 1 5 (suc n) + emb (Z.- (+ 24000)) * c 3 3 (suc n) ≃
    (emb (+ 210) + emb (Z.- (+ 420)) * NR.natReal (suc n)) * s 5 (suc n) +
      emb (+ 10) * s 1 (suc n) + emb (+ 200) * s 3 (suc n)
c15R n =
  let m = suc n in
  lift (add (mul (K 5040) (mixed 1 5 m)) (mul (negK 24000) (mixed 3 3 m)))
    (add (add (mul (add (K 210) (mul (negK 420) (K m))) (S 5 m)) (mul (K 10) (S 1 m)))
      (mul (K 200) (S 3 m))) (A.c15Scaled n)

-- Generic literal Euler readout on positive grades.
eulerValue : (f : Series) (a : ℤ) (k : Nat) →
  ((n : Nat) → f (suc n) ≃ emb a * s k (suc n)) →
  (n : Nat) → U.D 1 f (suc n) ≃ NR.natReal (suc n) * (emb a * s k (suc n))
eulerValue f a k h n =
  P.*-cong (P.*-identityˡ (NR.natReal (suc n))) (h n)

-- Explicitly reduce the three original rows using the integer theorem
-- at the same index. Constants are rationals; no division by a stream.
ramanujanE : F.RamanujanE
ramanujanE zero =
  P.≃-trans (U.D0 E) (P.≃-symm (U.right0
    (P.≃-trans (P.+-cong (P.≃-trans (Row.cauchyCoefficientZero E E) U.unitMul) P.≃-refl)
      (P.+-inverseʳ R.1ℝ))))
ramanujanE (suc n) =
  let m = NR.natReal (suc n)
      a = s 1 (suc n)
      b = s 3 (suc n)
      v = c 1 1 (suc n)
      open P.ℝ-Solver
      p = solve 3 (λ m a b → m ⊗ (Κ ((Z.- (+ 24)) / 1) ⊗ a) ⊜
        Κ (+ 1 / 12) ⊗ (Κ ((Z.- (+ 48)) / 1) ⊗ a ⊕ Κ (+ 48 / 1) ⊗
        (Κ (+ 5 / 1) ⊗ b ⊕ (Κ (+ 1 / 1) ⊕ Κ ((Z.- (+ 6)) / 1) ⊗ m) ⊗ a) ⊖ Κ (+ 240 / 1) ⊗ b))
        P.≃-refl m a b
      q = solve 3 (λ a b v → Κ (+ 1 / 12) ⊗
        (Κ ((Z.- (+ 48)) / 1) ⊗ a ⊕ Κ (+ 48 / 1) ⊗ (Κ (+ 12 / 1) ⊗ v) ⊖ Κ (+ 240 / 1) ⊗ b)
        ⊜ Κ (+ 1 / 12) ⊗ ((Κ ((Z.- (+ 24)) / 1) ⊗ a ⊕ Κ ((Z.- (+ 24)) / 1) ⊗ a ⊕
        (Κ ((Z.- (+ 24)) / 1) ⊗ Κ ((Z.- (+ 24)) / 1)) ⊗ v) ⊖ Κ (+ 240 / 1) ⊗ b))
        P.≃-refl a b v
  in P.≃-trans (eulerValue E (Z.- (+ 24)) 1 eValue n)
    (P.≃-trans p
      (P.≃-trans (P.*-congˡ (P.+-cong
        (P.+-cong P.≃-refl (P.*-congˡ (P.≃-symm (c11R n)))) P.≃-refl))
        (P.≃-trans q (P.*-congˡ (P.+-cong (P.≃-symm (ee n)) (P.-‿cong (P.≃-symm (xValue n))))))))

ramanujanX : F.RamanujanX
ramanujanX zero =
  P.≃-trans (U.D0 X) (P.≃-symm (U.right0
    (P.≃-trans (P.+-cong (P.≃-trans (Row.cauchyCoefficientZero E X) U.unitMul) P.≃-refl)
      (P.+-inverseʳ R.1ℝ))))
ramanujanX (suc n) =
  let m = NR.natReal (suc n)
      a = s 1 (suc n)
      b = s 3 (suc n)
      d = s 5 (suc n)
      v = c 1 3 (suc n)
      open P.ℝ-Solver
      p = solve 4 (λ m a b d → m ⊗ (Κ (+ 240 / 1) ⊗ b) ⊜
        Κ (+ 1 / 3) ⊗ (Κ ((Z.- (+ 24)) / 1) ⊗ a ⊕ Κ (+ 240 / 1) ⊗ b ⊕
        Κ ((Z.- (+ 24)) / 1) ⊗ (Κ (+ 21 / 1) ⊗ d ⊕
        (Κ (+ 10 / 1) ⊕ Κ ((Z.- (+ 30)) / 1) ⊗ m) ⊗ b ⊕ Κ ((Z.- (+ 1)) / 1) ⊗ a)
        ⊖ Κ ((Z.- (+ 504)) / 1) ⊗ d))
        P.≃-refl m a b d
      q = solve 4 (λ a b d v → Κ (+ 1 / 3) ⊗
        (Κ ((Z.- (+ 24)) / 1) ⊗ a ⊕ Κ (+ 240 / 1) ⊗ b ⊕
        Κ ((Z.- (+ 24)) / 1) ⊗ (Κ (+ 240 / 1) ⊗ v) ⊖ Κ ((Z.- (+ 504)) / 1) ⊗ d)
        ⊜ Κ (+ 1 / 3) ⊗
        ((Κ ((Z.- (+ 24)) / 1) ⊗ a ⊕ Κ (+ 240 / 1) ⊗ b ⊕
        (Κ ((Z.- (+ 24)) / 1) ⊗ Κ (+ 240 / 1)) ⊗ v) ⊖ Κ ((Z.- (+ 504)) / 1) ⊗ d))
        P.≃-refl a b d v
  in P.≃-trans (eulerValue X (+ 240) 3 xValue n)
    (P.≃-trans p
      (P.≃-trans (P.*-congˡ (P.+-cong
        (P.+-cong P.≃-refl (P.*-congˡ (P.≃-symm (c13R n)))) P.≃-refl))
        (P.≃-trans q (P.*-congˡ (P.+-cong (P.≃-symm (ex n)) (P.-‿cong (P.≃-symm (yValue n))))))))

ramanujanY : F.RamanujanY
ramanujanY zero =
  P.≃-trans (U.D0 Y) (P.≃-symm (U.right0
    (P.≃-trans (P.+-cong (P.≃-trans (Row.cauchyCoefficientZero E Y) U.unitMul)
      (P.-‿cong (P.≃-trans (Row.cauchyCoefficientZero X X) U.unitMul)))
      (P.+-inverseʳ R.1ℝ))))
ramanujanY (suc n) =
  let m = NR.natReal (suc n)
      a = s 1 (suc n)
      b = s 3 (suc n)
      d = s 5 (suc n)
      v = c 1 5 (suc n)
      w = c 3 3 (suc n)
      open P.ℝ-Solver
      p = solve 4 (λ m a b d → m ⊗ (Κ ((Z.- (+ 504)) / 1) ⊗ d) ⊜
        Κ (+ 1 / 2) ⊗ (Κ ((Z.- (+ 24)) / 1) ⊗ a ⊖ Κ (+ 504 / 1) ⊗ d ⊖ Κ (+ 480 / 1) ⊗ b ⊕
        Κ (+ 12 / 5) ⊗ ((Κ (+ 210 / 1) ⊕ Κ ((Z.- (+ 420)) / 1) ⊗ m) ⊗ d ⊕
        Κ (+ 10 / 1) ⊗ a ⊕ Κ (+ 200 / 1) ⊗ b))) P.≃-refl m a b d
      q = solve 5 (λ a b d v w → Κ (+ 1 / 2) ⊗
        (Κ ((Z.- (+ 24)) / 1) ⊗ a ⊖ Κ (+ 504 / 1) ⊗ d ⊖ Κ (+ 480 / 1) ⊗ b ⊕
        Κ (+ 12 / 5) ⊗ (Κ (+ 5040 / 1) ⊗ v ⊕ Κ ((Z.- (+ 24000)) / 1) ⊗ w))
        ⊜ Κ (+ 1 / 2) ⊗
        ((Κ ((Z.- (+ 24)) / 1) ⊗ a ⊕ Κ ((Z.- (+ 504)) / 1) ⊗ d ⊕
        (Κ ((Z.- (+ 24)) / 1) ⊗ Κ ((Z.- (+ 504)) / 1)) ⊗ v) ⊖
        (Κ (+ 240 / 1) ⊗ b ⊕ Κ (+ 240 / 1) ⊗ b ⊕ (Κ (+ 240 / 1) ⊗ Κ (+ 240 / 1)) ⊗ w)))
        P.≃-refl a b d v w
  in P.≃-trans (eulerValue Y (Z.- (+ 504)) 5 yValue n)
    (P.≃-trans p
      (P.≃-trans (P.*-congˡ (P.+-cong P.≃-refl (P.*-congˡ (P.≃-symm (c15R n)))))
        (P.≃-trans q (P.*-congˡ (P.+-cong (P.≃-symm (ey n)) (P.-‿cong (P.≃-symm (xx n))))))))
