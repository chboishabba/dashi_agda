module DASHI.Moonshine.JInvariantBishopHyperQCoefficientUniquenessExact where

-- SOURCE-WRITTEN, UNCOMPILED. Specialize the existing finite Cauchy
-- row owner to the denominator-cleared third-order q-ODE.
-- All-index normalized coefficient uniqueness, without division by q,
-- z, a derivative, or invoking a classical analytic identity theorem.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (refl)
open import Relation.Nullary.Decidable.Core using (yes; no)
open import Data.Nat.Base using (_≤_; z≤n; s≤s)
import Data.Nat.Properties as NP
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
import Real as R
open R using (ℝ; _≃_; _+_; _-_; _*_; _⋆)
import RealProperties as P
import DASHI.Foundations.BishopFiniteCauchyRowReindexExact as C
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Moonshine.JInvariantEisensteinIncrementCoefficientBoundExact as Coeff

Series : Set
Series = Nat → ℝ

infixl 6 _⊕s_ _⊖s_
infixl 7 _⊗s_
_⊕s_ _⊖s_ _⊗s_ : Series → Series → Series
(f ⊕s g) n = f n + g n
(f ⊖s g) n = f n - g n
_⊗s_ = C.cauchyCoefficient

scale : ℝ → Series → Series
scale a f n = a * f n

D : Nat → Series → Series
D d f n = R.pow (NR.natReal n) d * f n

X Y : Series
X zero = R.1ℝ
X (suc n) = NR.natReal (Coeff.e4IncrementCoefficient n)
Y zero = R.1ℝ
Y (suc n) = R.- (NR.natReal (Coeff.e6IncrementCoefficient n))

X2 X3 Y2 Y3 disc A B : Series
X2 = X ⊗s X
X3 = X2 ⊗s X
Y2 = Y ⊗s Y
Y3 = Y2 ⊗s Y
disc = X3 ⊖s Y2
A = (Y ⊗s D 1 X) ⊖s (X ⊗s D 1 Y)
B = (Y ⊗s D 1 A) ⊖s scale ((+ 2 / 1) ⋆) (A ⊗s D 1 Y)

-- For L=(X/Y)D, z=(X^3-Y^2)/X^3, the following
-- is the cleared form of (1-z)L^3 F-z(3L^2 F/2+23LF/36+5F/72).
-- Multiply by 72 X^3 Y^3; all coefficients remain literal.
P3 P2 P1 P0 : Series
P3 = scale ((+ 72 / 1) ⋆) (X3 ⊗s Y2)
P2 = scale ((+ 108 / 1) ⋆) (X2 ⊗s Y ⊗s (scale ((+ 2 / 1) ⋆) A ⊖s disc))
P1 = scale ((+ 72 / 1) ⋆) (X ⊗s ((A ⊗s A) ⊕s (X ⊗s B)))
  ⊖s scale ((+ 108 / 1) ⋆) (X ⊗s disc ⊗s A)
  ⊖s scale ((+ 46 / 1) ⋆) (X ⊗s Y2 ⊗s disc)
P0 = scale (R.- ((+ 5 / 1) ⋆)) (Y3 ⊗s disc)

mul0 : ∀ {f g : Series} {a b : ℝ} → f zero ≃ a → g zero ≃ b →
  (f ⊗s g) zero ≃ (a * b)
mul0 {f} {g} hf hg = P.≃-trans (C.cauchyCoefficientZero f g) (P.*-cong hf hg)

unitMul : R.1ℝ * R.1ℝ ≃ R.1ℝ
unitMul = P.*-identityʳ R.1ℝ

x20 : X2 zero ≃ R.1ℝ
x20 = P.≃-trans (mul0 {f = X} {g = X} P.≃-refl P.≃-refl) unitMul
x30 : X3 zero ≃ R.1ℝ
x30 = P.≃-trans (mul0 {f = X2} {g = X} x20 P.≃-refl) unitMul
y20 : Y2 zero ≃ R.1ℝ
y20 = P.≃-trans (mul0 {f = Y} {g = Y} P.≃-refl P.≃-refl) unitMul
y30 : Y3 zero ≃ R.1ℝ
y30 = P.≃-trans (mul0 {f = Y2} {g = Y} y20 P.≃-refl) unitMul

sub0 : ∀ {x y : ℝ} → x ≃ R.0ℝ → y ≃ R.0ℝ → (x - y) ≃ R.0ℝ
sub0 hx hy = P.≃-trans (P.+-cong hx (P.-‿cong hy))
  (let open P.ℝ-Solver in solve 0 (Κ Q.0ℚᵘ ⊖ Κ Q.0ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl)

add0 : ∀ {x y : ℝ} → x ≃ R.0ℝ → y ≃ R.0ℝ → (x + y) ≃ R.0ℝ
add0 hx hy = P.≃-trans (P.+-cong hx hy) (P.+-identityʳ R.0ℝ)

right0 : ∀ {x y : ℝ} → y ≃ R.0ℝ → (x * y) ≃ R.0ℝ
right0 {x} h = P.≃-trans (P.*-congˡ h) (P.*-zeroʳ x)

disc0 : disc zero ≃ R.0ℝ
disc0 = P.≃-trans (P.+-cong x30 (P.-‿cong y20))
  (let open P.ℝ-Solver in solve 0 (Κ Q.1ℚᵘ ⊖ Κ Q.1ℚᵘ ⊜ Κ Q.0ℚᵘ) P.≃-refl)

D0 : (f : Series) → D 1 f zero ≃ R.0ℝ
D0 f = let open P.ℝ-Solver in solve 1 (λ x →
  (Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ) ⊗ x ⊜ Κ Q.0ℚᵘ) P.≃-refl (f zero)

a0 : A zero ≃ R.0ℝ
a0 = sub0
  (P.≃-trans (C.cauchyCoefficientZero Y (D 1 X)) (right0 (D0 X)))
  (P.≃-trans (C.cauchyCoefficientZero X (D 1 Y)) (right0 (D0 Y)))

-- Constant-term multiplication with zero second factor, using the
-- same Cauchy row rather than a second convolution implementation.
mulR0 : (f g : Series) → g zero ≃ R.0ℝ → (f ⊗s g) zero ≃ R.0ℝ
mulR0 f g hg = P.≃-trans (C.cauchyCoefficientZero f g) (right0 hg)

b0 : B zero ≃ R.0ℝ
b0 = sub0 (mulR0 Y (D 1 A) (D0 A))
  (right0 (mulR0 A (D 1 Y) (D0 Y)))

p30 : P3 zero ≃ ((+ 72 / 1) ⋆)
p30 = P.≃-trans (P.*-congˡ (P.≃-trans
  (mul0 {f = X3} {g = Y2} x30 y20) unitMul))
  (P.*-identityʳ ((+ 72 / 1) ⋆))

p20 : P2 zero ≃ R.0ℝ
p20 = right0 (mulR0 (X2 ⊗s Y) (scale ((+ 2 / 1) ⋆) A ⊖s disc)
  (sub0 (right0 a0) disc0))

p10 : P1 zero ≃ R.0ℝ
p10 = sub0 (sub0
  (right0 (mulR0 X ((A ⊗s A) ⊕s (X ⊗s B))
    (add0 (mulR0 A A a0) (mulR0 X B b0))))
  (right0 (mulR0 (X ⊗s disc) A a0)))
  (right0 (mulR0 (X ⊗s Y2) disc disc0))

p00 : P0 zero ≃ R.0ℝ
p00 = right0 (mulR0 Y3 disc disc0)

-- A single finite-prefix equality suffices to compare every
-- coefficient of a Cauchy row. This follows the original head law.
PrefixEq : Series → Series → Nat → Set
PrefixEq f g n = (k : Nat) → k ≤ n → f k ≃ g k

convPrefix : (a f g : Series) (n : Nat) → PrefixEq f g n →
  (a ⊗s f) n ≃ (a ⊗s g) n
convPrefix a f g zero h =
  P.≃-trans (C.cauchyCoefficientZero a f)
    (P.≃-trans (P.*-congˡ (h zero z≤n))
      (P.≃-symm (C.cauchyCoefficientZero a g)))
convPrefix a f g (suc n) h =
  P.≃-trans (C.cauchyCoefficientSuccessor a f n)
    (P.≃-trans (P.+-cong (P.*-congˡ (h (suc n) NP.≤-refl))
      (convPrefix (C.shift a) f g n (λ k hk → h k (NP.≤-step hk))))
      (P.≃-symm (C.cauchyCoefficientSuccessor a g n)))

Dprefix : (d : Nat) {f g : Series} {n : Nat} → PrefixEq f g n →
  PrefixEq (D d f) (D d g) n
Dprefix d h k hk = P.*-congˡ (h k hk)

residual : Series → Nat → ℝ
residual f n = (P3 ⊗s D 3 f) n + (P2 ⊗s D 2 f) n +
  (P1 ⊗s D 1 f) n + (P0 ⊗s f) n

tail : Series → Nat → ℝ
tail f n = (C.shift P3 ⊗s D 3 f) n + (C.shift P2 ⊗s D 2 f) n +
  (C.shift P1 ⊗s D 1 f) n + (C.shift P0 ⊗s f) n

lead : Nat → ℝ
lead n = ((+ 72 / 1) ⋆) * R.pow (NR.natReal n) 3

leadPositive : (n : Nat) → R.Positive (lead (suc n))
leadPositive n = P.posx,y⇒posx*y (P.posp⇒posp⋆ (+ 72 / 1) (QP.positive⁻¹ (+ 72 / 1)))
  (P.posx,y⇒posx*y (P.posx,y⇒posx*y (P.posx,y⇒posx*y
    (P.posp⇒posp⋆ Q.1ℚᵘ (QP.positive⁻¹ Q.1ℚᵘ)) p) p) p)
  where
  p : R.Positive (NR.natReal (suc n))
  p = P.posp⇒posp⋆ (+ (suc n) / 1) (QP.positive⁻¹ (+ (suc n) / 1))

head3 : (f : Series) (n : Nat) →
  (P3 ⊗s D 3 f) (suc n) ≃
    (lead (suc n) * f (suc n) + (C.shift P3 ⊗s D 3 f) n)
head3 f n = P.≃-trans (C.cauchyCoefficientSuccessor P3 (D 3 f) n)
  (P.+-cong (P.≃-trans (P.*-congʳ p30)
    (P.≃-symm (P.*-assoc ((+ 72 / 1) ⋆) (R.pow (NR.natReal (suc n)) 3) (f (suc n)))))
    P.≃-refl)

zeroHead : (a f : Series) → a zero ≃ R.0ℝ → (n : Nat) →
  (a ⊗s f) (suc n) ≃ (C.shift a ⊗s f) n
zeroHead a f h n =
  P.≃-trans (C.cauchyCoefficientSuccessor a f n)
    (P.≃-trans (P.+-cong
      (P.≃-trans (P.*-congʳ h) (P.*-zeroˡ (f (suc n)))) P.≃-refl)
      (P.+-identityˡ ((C.shift a ⊗s f) n)))

residualHead : (f : Series) (n : Nat) →
  residual f (suc n) ≃ (lead (suc n) * f (suc n) + tail f n)
residualHead f n =
  P.≃-trans
    (P.+-cong (P.+-cong (P.+-cong (head3 f n)
      (zeroHead P2 (D 2 f) p20 n)) (zeroHead P1 (D 1 f) p10 n))
      (zeroHead P0 f p00 n))
    (let open P.ℝ-Solver in solve 5 (λ a b c d e →
      (a ⊕ b) ⊕ c ⊕ d ⊕ e ⊜ a ⊕ (b ⊕ c ⊕ d ⊕ e))
      P.≃-refl (lead (suc n) * f (suc n))
      ((C.shift P3 ⊗s D 3 f) n) ((C.shift P2 ⊗s D 2 f) n)
      ((C.shift P1 ⊗s D 1 f) n) ((C.shift P0 ⊗s f) n))

tailCong : (f g : Series) (n : Nat) → PrefixEq f g n → tail f n ≃ tail g n
tailCong f g n h = P.+-cong
  (P.+-cong (P.+-cong
    (convPrefix (C.shift P3) (D 3 f) (D 3 g) n (Dprefix 3 h))
    (convPrefix (C.shift P2) (D 2 f) (D 2 g) n (Dprefix 2 h)))
    (convPrefix (C.shift P1) (D 1 f) (D 1 g) n (Dprefix 1 h)))
  (convPrefix (C.shift P0) f g n h)

-- Both normalized streams must satisfy the actual cleared ODE.
-- No proof that the candidate streams satisfy it is assumed here.
Solution : Series → Set
Solution f = (n : Nat) → residual f n ≃ R.0ℝ

nextEqual : (f g : Series) → Solution f → Solution g →
  (n : Nat) → PrefixEq f g n → f (suc n) ≃ g (suc n)
nextEqual f g hf hg n h =
  let
    a = lead (suc n) * f (suc n)
    b = lead (suc n) * g (suc n)
    t = tail f n
    eq : (a + t) ≃ (b + t)
    eq = P.≃-trans (P.≃-symm (residualHead f n))
      (P.≃-trans (hf (suc n)) (P.≃-trans (P.≃-symm (hg (suc n)))
        (P.≃-trans (residualHead g n) (P.+-congˡ (P.≃-symm (tailCong f g n h))))))
    open P.ℝ-Solver
    scaledEq : a ≃ b
    scaledEq = P.≃-trans (solve 2 (λ a t → a ⊜ (a ⊕ t) ⊖ t) P.≃-refl a t)
      (P.≃-trans (P.+-congʳ eq)
        (solve 2 (λ b t → (b ⊕ t) ⊖ t ⊜ b) P.≃-refl b t))
  in N.cancelLeft (lead (suc n)) (leadPositive n) scaledEq

-- Structural induction on the prefix length, not on a finite test
-- cutoff or an assumed analytic uniqueness axiom.
prefixUnique : (f g : Series) → Solution f → Solution g →
  f zero ≃ g zero → (n : Nat) → PrefixEq f g n
prefixUnique f g hf hg h0 zero zero hk = h0
prefixUnique f g hf hg h0 zero (suc k) ()
prefixUnique f g hf hg h0 (suc n) k hk with k NP.≟ suc n
... | yes refl = nextEqual f g hf hg n (prefixUnique f g hf hg h0 n)
... | no neq =
  prefixUnique f g hf hg h0 n k (NP.≤-pred (NP.≤∧≢⇒< hk neq))

allCoefficientsUnique : (f g : Series) → Solution f → Solution g →
  f zero ≃ g zero → (n : Nat) → f n ≃ g n
allCoefficientsUnique f g hf hg h0 n = prefixUnique f g hf hg h0 n n NP.≤-refl
