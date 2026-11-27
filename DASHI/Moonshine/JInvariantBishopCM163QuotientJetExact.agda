module DASHI.Moonshine.JInvariantBishopCM163QuotientJetExact where

-- Source-written: formal two-jet of the original normalized quotient,
-- using the existing evaluated first/second Euler streams and bracket.
-- This is the coefficient jet; its identification with the analytic
-- reciprocal Mobius germ remains a same-object analytic obligation.
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Sum.Base using (inj₁)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import Inverse as Inv
import DASHI.Moonshine.JInvariantBishopCM163LiteralBracketExact as B
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163DiskCrossCoefficientExact as Cancel
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N

X Y x1 y1 x2 y2 j d d1 d2 n0 n1 n2 : ℝ
X = J.X
Y = J.Y
x1 = B.Readout.value B.x1
y1 = B.Readout.value B.y1
x2 = B.Readout.value B.x2
y2 = B.Readout.value B.y2
j = Guard.Root.j
d = N.cube X - N.sq Y
d1 = ((+ 3 / 1) ⋆) * N.sq X * x1 - ((+ 2 / 1) ⋆) * Y * y1
d2 = ((+ 6 / 1) ⋆) * X * x1 * x1 + ((+ 3 / 1) ⋆) * N.sq X * x2 -
  ((+ 2 / 1) ⋆) * y1 * y1 - ((+ 2 / 1) ⋆) * Y * y2
n0 = ((+ 1728 / 1) ⋆) * N.cube X
n1 = ((+ 5184 / 1) ⋆) * N.sq X * x1
n2 = ((+ 10368 / 1) ⋆) * X * x1 * x1 + ((+ 5184 / 1) ⋆) * N.sq X * x2

negativeD : d R.< R.0ℝ
negativeD = P.<-respʳ-≃
  (P.+-inverseʳ (N.sq Y))
  (P.+-monoˡ-< (R.- N.sq Y) (P.≤-<-trans Guard.xCubeBelowOne Guard.oneBelowYSquare))

dApart : R._≄0 d
dApart = inj₁ negativeD

id : ℝ
id = Inv._⁻¹ d dApart

dCancel : (v : ℝ) → d * (id * v) ≃ v
dCancel v = P.≃-trans (P.≃-symm (P.*-assoc d id v))
  (P.≃-trans (P.*-congʳ (Inv.*-inverseʳ d dApart)) (P.*-identityˡ v))

-- The zeroth quotient is the original guarded j, including its sign.
q0 : d * j ≃ n0
q0 =
  P.≃-trans
    (let open P.ℝ-Solver in solve 2 (λ d j →
      d ⊗ j ⊜ Κ (+ 1728 / 1) ⊗ (j ⊗ (Κ (+ 1 / 1728) ⊗ d)))
      P.≃-refl d j)
    (P.≃-trans (P.*-congˡ (P.*-congˡ (P.≃-symm CM.Selected.deltaRe)))
      (P.*-congˡ Guard.Root.jCross))

-- Construct the two coefficient jets by exact division by the same
-- guarded discriminant. This is the unique two-jet quotient rule.
a b : ℝ
a = id * (n1 - d1 * j)
b = id * (n2 - ((+ 2 / 1) ⋆) * d1 * a - d2 * j)

q1 : d * a ≃ (n1 - d1 * j)
q1 = dCancel (n1 - d1 * j)

q2 : d * b ≃ (n2 - ((+ 2 / 1) ⋆) * d1 * a - d2 * j)
q2 = dCancel (n2 - ((+ 2 / 1) ⋆) * d1 * a - d2 * j)

br : ℝ
br = ((+ 3 / 1) ⋆) * Y * x1 - ((+ 2 / 1) ⋆) * X * y1

br1 : ℝ
br1 = ((+ 3 / 1) ⋆) * (y1 * x1 + Y * x2) -
  ((+ 2 / 1) ⋆) * (x1 * y1 + X * y2)

brEq : br ≃ d
brEq = P.≃-trans
  (let open P.ℝ-Solver in solve 4 (λ x y u v →
    Κ (+ 3 / 1) ⊗ y ⊗ u ⊖ Κ (+ 2 / 1) ⊗ x ⊗ v
    ⊜ (y ⊗ u ⊕ y ⊗ u ⊕ y ⊗ u) ⊖ (x ⊗ v ⊕ x ⊗ v))
    P.≃-refl X Y x1 y1)
  B.bracketValue

br1Eq : br1 ≃ d1
br1Eq = P.≃-trans
  (let open P.ℝ-Solver in solve 6 (λ x y u v w z →
    Κ (+ 3 / 1) ⊗ (v ⊗ u ⊕ y ⊗ w) ⊖ Κ (+ 2 / 1) ⊗ (u ⊗ v ⊕ x ⊗ z)
    ⊜ (v ⊗ u ⊕ y ⊗ w) ⊕ (v ⊗ u ⊕ y ⊗ w) ⊕ (v ⊗ u ⊕ y ⊗ w)
       ⊖ ((u ⊗ v ⊕ x ⊗ z) ⊕ (u ⊗ v ⊕ x ⊗ z)))
    P.≃-refl X Y x1 y1 x2 y2)
  (P.≃-trans B.dBracketValue
    (let open P.ℝ-Solver in solve 4 (λ x y u v →
      ((u ⊗ x ⊕ x ⊗ u) ⊗ x ⊕ (x ⊗ x) ⊗ u) ⊖ (v ⊗ y ⊕ y ⊗ v)
      ⊜ Κ (+ 3 / 1) ⊗ (x ⊗ x) ⊗ u ⊖ Κ (+ 2 / 1) ⊗ y ⊗ v)
      P.≃-refl X Y x1 y1))

-- All five cleared equations, each with its signed zero preserved.
q0z : (n0 - d * j) ≃ R.0ℝ
q0z = P.≃-trans (P.+-cong (P.≃-symm q0) P.≃-refl) (P.+-inverseʳ (d * j))

q1z : (d * a + d1 * j - n1) ≃ R.0ℝ
q1z = P.≃-trans (P.+-cong (P.+-cong q1 P.≃-refl) P.≃-refl)
  (let open P.ℝ-Solver in solve 3 (λ n d j → (n ⊖ d ⊗ j) ⊕ d ⊗ j ⊖ n ⊜ Κ Q.0ℚᵘ)
    P.≃-refl n1 d1 j)

q2z : (d * b + ((+ 2 / 1) ⋆) * d1 * a + d2 * j - n2) ≃ R.0ℝ
q2z = P.≃-trans (P.+-cong (P.+-cong (P.+-cong q2 P.≃-refl) P.≃-refl) P.≃-refl)
  (let open P.ℝ-Solver in solve 5 (λ n u v w j →
    (n ⊖ Κ (+ 2 / 1) ⊗ u ⊗ v ⊖ w ⊗ j) ⊕ Κ (+ 2 / 1) ⊗ u ⊗ v ⊕ w ⊗ j ⊖ n
    ⊜ Κ Q.0ℚᵘ) P.≃-refl n2 d1 a d2 j)

s0 : ℝ
s0 = ((+ 3 / 1) ⋆) * x1 * d - X * d1 + d * Y

s1 : ℝ
s1 = ((+ 3 / 1) ⋆) * x2 * d + ((+ 2 / 1) ⋆) * x1 * d1 - X * d2 + d1 * Y + d * y1

s0z : s0 ≃ R.0ℝ
s0z =
  P.≃-trans
    (let open P.ℝ-Solver in solve 4 (λ x y u v →
      Κ (+ 3 / 1) ⊗ u ⊗ (x ⊗ x ⊗ x ⊖ y ⊗ y) ⊖
      x ⊗ (Κ (+ 3 / 1) ⊗ (x ⊗ x) ⊗ u ⊖ Κ (+ 2 / 1) ⊗ y ⊗ v) ⊕
      (x ⊗ x ⊗ x ⊖ y ⊗ y) ⊗ y
      ⊜ y ⊗ ((x ⊗ x ⊗ x ⊖ y ⊗ y) ⊖ (Κ (+ 3 / 1) ⊗ y ⊗ u ⊖ Κ (+ 2 / 1) ⊗ x ⊗ v)))
      P.≃-refl X Y x1 y1)
    (P.≃-trans (P.*-congˡ (P.+-cong P.≃-refl (P.-‿cong brEq)))
      (P.≃-trans (P.*-congˡ (P.+-inverseʳ d)) (P.*-zeroʳ Y)))

s1z : s1 ≃ R.0ℝ
s1z =
  P.≃-trans
    (let open P.ℝ-Solver in solve 6 (λ x y u v w z →
      Κ (+ 3 / 1) ⊗ w ⊗ (x ⊗ x ⊗ x ⊖ y ⊗ y) ⊕
      Κ (+ 2 / 1) ⊗ u ⊗ (Κ (+ 3 / 1) ⊗ (x ⊗ x) ⊗ u ⊖ Κ (+ 2 / 1) ⊗ y ⊗ v) ⊖
      x ⊗ (Κ (+ 6 / 1) ⊗ x ⊗ u ⊗ u ⊕ Κ (+ 3 / 1) ⊗ (x ⊗ x) ⊗ w
        ⊖ Κ (+ 2 / 1) ⊗ v ⊗ v ⊖ Κ (+ 2 / 1) ⊗ y ⊗ z) ⊕
      (Κ (+ 3 / 1) ⊗ (x ⊗ x) ⊗ u ⊖ Κ (+ 2 / 1) ⊗ y ⊗ v) ⊗ y ⊕
      (x ⊗ x ⊗ x ⊖ y ⊗ y) ⊗ v
      ⊜ v ⊗ ((x ⊗ x ⊗ x ⊖ y ⊗ y) ⊖ (Κ (+ 3 / 1) ⊗ y ⊗ u ⊖ Κ (+ 2 / 1) ⊗ x ⊗ v)) ⊕
      y ⊗ ((Κ (+ 3 / 1) ⊗ (x ⊗ x) ⊗ u ⊖ Κ (+ 2 / 1) ⊗ y ⊗ v) ⊖
        (Κ (+ 3 / 1) ⊗ (v ⊗ u ⊕ y ⊗ w) ⊖ Κ (+ 2 / 1) ⊗ (u ⊗ v ⊕ x ⊗ z))))
      P.≃-refl X Y x1 y1 x2 y2)
    (P.≃-trans (P.+-cong
      (P.*-congˡ (P.≃-trans (P.+-cong P.≃-refl (P.-‿cong brEq)) (P.+-inverseʳ d)))
      (P.*-congˡ (P.≃-trans (P.+-cong P.≃-refl (P.-‿cong br1Eq)) (P.+-inverseʳ d1))))
      (P.≃-trans (P.+-cong (P.*-zeroʳ y1) (P.*-zeroʳ Y)) (P.+-identityʳ R.0ℝ)))

-- Denominator-free first identity and its exact differentiated identity.
-- The solver normalizes only polynomial combinations of the already
-- established zero residuals; it cannot invent an analytic equality.
firstZ : (X * a + j * Y) ≃ R.0ℝ
firstZ = Cancel.cancelApart d dApart
  (P.≃-trans
    (let open P.ℝ-Solver in solve 7 (λ x y u d e a j → 
      d ⊗ (x ⊗ a ⊕ j ⊗ y) ⊜
      x ⊗ (d ⊗ a ⊕ e ⊗ j ⊖ Κ (+ 5184 / 1) ⊗ (x ⊗ x) ⊗ u) ⊕
      Κ (+ 3 / 1) ⊗ u ⊗ (Κ (+ 1728 / 1) ⊗ (x ⊗ x ⊗ x) ⊖ d ⊗ j) ⊕
      j ⊗ (Κ (+ 3 / 1) ⊗ u ⊗ d ⊖ x ⊗ e ⊕ d ⊗ y))
      P.≃-refl X Y x1 d d1 a j)
    (P.≃-trans (P.+-cong (P.+-cong (P.*-congˡ q1z) (P.*-congˡ q0z)) (P.*-congˡ s0z))
      (let open P.ℝ-Solver in solve 4 (λ x u j d →
        x ⊗ Κ Q.0ℚᵘ ⊕ Κ (+ 3 / 1) ⊗ u ⊗ Κ Q.0ℚᵘ ⊕ j ⊗ Κ Q.0ℚᵘ
        ⊜ d ⊗ Κ Q.0ℚᵘ) P.≃-refl X x1 j d)))

-- Differentiate the same cleared relation, not an independent square.
-- Keeping the first residual explicitly makes the proof bidirectional.
secondZ : (X * b + (x1 + Y) * a + j * y1) ≃ R.0ℝ
secondZ =
  let q1neg : (n1 - d1 * j - d * a) ≃ R.0ℝ
      q1neg = P.≃-trans (P.+-cong (P.≃-symm q1) P.≃-refl) (P.+-inverseʳ (d * a))
      h : (d1 * (X * a + j * Y) + d * (X * b + (x1 + Y) * a + j * y1)) ≃ R.0ℝ
      h = P.≃-trans
        (let open P.ℝ-Solver in solve 11 (λ x y u v w d e f j a b →
          e ⊗ (x ⊗ a ⊕ j ⊗ y) ⊕ d ⊗ (x ⊗ b ⊕ (u ⊕ y) ⊗ a ⊕ j ⊗ v)
          ⊜ u ⊗ (d ⊗ a ⊕ e ⊗ j ⊖ Κ (+ 5184 / 1) ⊗ (x ⊗ x) ⊗ u) ⊕
            x ⊗ (d ⊗ b ⊕ Κ (+ 2 / 1) ⊗ e ⊗ a ⊕ f ⊗ j ⊖
              (Κ (+ 10368 / 1) ⊗ x ⊗ u ⊗ u ⊕ Κ (+ 5184 / 1) ⊗ (x ⊗ x) ⊗ w)) ⊕
            Κ (+ 3 / 1) ⊗ w ⊗ (Κ (+ 1728 / 1) ⊗ (x ⊗ x ⊗ x) ⊖ d ⊗ j) ⊕
            Κ (+ 3 / 1) ⊗ u ⊗ (Κ (+ 5184 / 1) ⊗ (x ⊗ x) ⊗ u ⊖ e ⊗ j ⊖ d ⊗ a) ⊕
            a ⊗ (Κ (+ 3 / 1) ⊗ u ⊗ d ⊖ x ⊗ e ⊕ d ⊗ y) ⊕
            j ⊗ (Κ (+ 3 / 1) ⊗ w ⊗ d ⊕ Κ (+ 2 / 1) ⊗ u ⊗ e ⊖ x ⊗ f ⊕ e ⊗ y ⊕ d ⊗ v))
          P.≃-refl X Y x1 y1 x2 d d1 d2 j a b)
        (P.≃-trans (P.+-cong (P.+-cong (P.+-cong (P.+-cong (P.+-cong
          (P.*-congˡ q1z) (P.*-congˡ q2z)) (P.*-congˡ q0z)) (P.*-congˡ q1neg))
          (P.*-congˡ s0z)) (P.*-congˡ s1z))
          (let open P.ℝ-Solver in solve 5 (λ x u w a j →
            u ⊗ Κ Q.0ℚᵘ ⊕ x ⊗ Κ Q.0ℚᵘ ⊕ Κ (+ 3 / 1) ⊗ w ⊗ Κ Q.0ℚᵘ ⊕
            Κ (+ 3 / 1) ⊗ u ⊗ Κ Q.0ℚᵘ ⊕ a ⊗ Κ Q.0ℚᵘ ⊕ j ⊗ Κ Q.0ℚᵘ
            ⊜ Κ Q.0ℚᵘ) P.≃-refl X x1 x2 a j))
  in Cancel.cancelApart d dApart
    (P.≃-trans (P.≃-symm (P.+-identityˡ (d * (X * b + (x1 + Y) * a + j * y1))))
      (P.≃-trans (P.+-cong (P.≃-symm (P.≃-trans (P.*-congˡ firstZ) (P.*-zeroʳ d1))) P.≃-refl)
        (P.≃-trans h (P.≃-symm (P.*-zeroʳ d)))))

first : J.CMRoot → J.FirstQJet a
first root =
  P.≃-trans
    (let open P.ℝ-Solver in solve 3 (λ x a t → x ⊗ a ⊜ (x ⊗ a ⊕ t) ⊖ t)
      P.≃-refl X a (j * Y))
    (P.≃-trans (P.+-cong firstZ P.≃-refl)
      (P.≃-trans (P.+-identityˡ (R.- (j * Y))) (P.-‿cong (P.*-congʳ root))))

-- Recover the signed scalar second formula from the actual quotient
-- derivative relation and the actual bracket at the same selected q.
second : J.CMRoot → J.SecondQJet b
second root =
  let xa : (X * a) ≃ R.- (j * Y)
      xa = P.≃-trans (first root) (P.-‿cong (P.*-congʳ (P.≃-symm root)))
      xb : (X * b) ≃ R.- ((x1 + Y) * a + j * y1)
      xb = P.≃-trans
        (let open P.ℝ-Solver in solve 3 (λ x b v → x ⊗ b ⊜ (x ⊗ b ⊕ v) ⊖ v)
          P.≃-refl X b ((x1 + Y) * a + j * y1))
        (P.≃-trans (P.+-cong
          (P.≃-trans (P.≃-symm (P.+-assoc (X * b) ((x1 + Y) * a) (j * y1))) secondZ) P.≃-refl)
          (P.+-identityˡ (R.- ((x1 + Y) * a + j * y1))))
      open P.ℝ-Solver
  in P.≃-trans
    (solve 2 (λ x b → Κ (+ 6 / 1) ⊗ (x ⊗ x) ⊗ b ⊜ Κ (+ 6 / 1) ⊗ x ⊗ (x ⊗ b))
      P.≃-refl X b)
    (P.≃-trans (P.*-congˡ xb)
      (P.≃-trans (solve 6 (λ x y u v j a →
        Κ (+ 6 / 1) ⊗ x ⊗ (⊝ ((u ⊕ y) ⊗ a ⊕ j ⊗ v))
        ⊜ (⊝ (Κ (+ 6 / 1) ⊗ (u ⊕ y) ⊗ (x ⊗ a))) ⊖ Κ (+ 6 / 1) ⊗ j ⊗ x ⊗ v)
        P.≃-refl X Y x1 y1 j a)
        (P.≃-trans (P.+-cong (P.-‿cong (P.*-congˡ xa)) P.≃-refl)
          (P.≃-trans (solve 5 (λ x y u v j →
            (⊝ (Κ (+ 6 / 1) ⊗ (u ⊕ y) ⊗ (⊝ (j ⊗ y)))) ⊖ Κ (+ 6 / 1) ⊗ j ⊗ x ⊗ v
            ⊜ j ⊗ (Κ (+ 6 / 1) ⊗ (y ⊗ y) ⊕ Κ (+ 3 / 1) ⊗
              (Κ (+ 3 / 1) ⊗ y ⊗ u ⊖ Κ (+ 2 / 1) ⊗ x ⊗ v) ⊖ Κ (+ 3 / 1) ⊗ y ⊗ u))
            P.≃-refl X Y x1 y1 j)
            (P.≃-trans (P.*-cong root (P.+-cong (P.+-cong P.≃-refl (P.*-congˡ brEq)) P.≃-refl))
              (solve 4 (λ x y u k →
                k ⊗ (Κ (+ 6 / 1) ⊗ (y ⊗ y) ⊕ Κ (+ 3 / 1) ⊗ (x ⊗ x ⊗ x ⊖ y ⊗ y)
                  ⊖ Κ (+ 3 / 1) ⊗ y ⊗ u)
                ⊜ k ⊗ (Κ (+ 3 / 1) ⊗ (x ⊗ x ⊗ x) ⊕ Κ (+ 3 / 1) ⊗ (y ⊗ y)
                  ⊖ y ⊗ (Κ (+ 3 / 1) ⊗ u)))
                P.≃-refl X Y x1 J.K))))))
