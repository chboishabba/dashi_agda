module DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact where

-- SOURCE-WRITTEN, UNCOMPILED. Reverse-solve the original E4/E6 coefficient
-- jets and signed CM correction. The analytic coefficient identities
-- remain inputs, not inferred from finite algebra or convergence.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Integer.Base using (+_)
import Data.Integer.Base as Z
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Moonshine.JInvariantBishopCM163E4JetPeriodExact as Jet
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as Guard
import DASHI.Moonshine.JInvariantBishopCM163RealSlicePeriodExact as Slice
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopChudnovskyNativeEulerLimitsExact as E
import DASHI.Foundations.BishopChudnovskyNativePeriodProductExact as End
import DASHI.Foundations.BishopChudnovskyRawCoordinateWeldExact as Raw
import DASHI.Foundations.BishopMachinArctanConstructionExact as M

X Y U W : ℝ
X = Jet.X
Y = Jet.Y
U = Jet.U
W = ((+ 2 / 1) ⋆) * C.re (Jet.J.e6EulerJet (suc zero))

d : ℝ
d = N.cube X - N.sq Y

-- The actual Rankin-Cohen bracket, interpreted over native reals.
Bracket : Set
Bracket = (Y * U - X * W) ≃ d

-- The derivative of z=1-Y²/X³ multiplied by X^4; this
-- definition does not assert derivative interpretation.
zNumerator : ℝ
zNumerator = Y * (Y * U - X * W)

ZFlow : Set
ZFlow = zNumerator ≃ (Y * d)

zFromBracket : Bracket → ZFlow
zFromBracket h = P.*-congˡ h

bracketFromZ : ZFlow → Bracket
bracketFromZ = N.cancelLeft Y Guard.yPositive

-- Forward/reverse hypergeometric flow after differentiation and
-- clearing X. The sign of H need not be assumed: multiply by H,
-- rewrite H²=X, and cancel the already-proved positive X.
HyperSquare : Set
HyperSquare = N.sq E.H ≃ X

ClearedHyperJet : Set
ClearedHyperJet = (N.six * E.H * Y * E.J₁) ≃ (X * U)

flowFromCleared : HyperSquare → ClearedHyperJet → Jet.Flow
flowFromCleared hs hj = N.cancelLeft X Guard.xPositive
  (P.≃-trans
    (P.*-congʳ (P.≃-symm hs))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 3 (λ h y j →
        (h ⊗ h) ⊗ (Κ (+ 6 / 1) ⊗ y ⊗ j)
        ⊜ h ⊗ (Κ (+ 6 / 1) ⊗ h ⊗ y ⊗ j))
        P.≃-refl E.H Y E.J₁)
      (P.≃-trans (P.*-congˡ hj)
        (let open P.ℝ-Solver in solve 3 (λ h x u →
          h ⊗ (x ⊗ u) ⊜ x ⊗ (h ⊗ u)) P.≃-refl E.H X U))))

clearedFromFlow : HyperSquare → Jet.Flow → ClearedHyperJet
clearedFromFlow hs hj =
  P.≃-trans
    (let open P.ℝ-Solver in solve 3 (λ h y j →
      Κ (+ 6 / 1) ⊗ h ⊗ y ⊗ j
      ⊜ h ⊗ (Κ (+ 6 / 1) ⊗ y ⊗ j)) P.≃-refl E.H Y E.J₁)
    (P.≃-trans (P.*-congˡ hj)
      (P.≃-trans (P.≃-symm (P.*-assoc E.H E.H U))
        (P.*-congʳ hs)))

-- If the actual chain derivative L has X L = Y J1 and
-- differentiated square gives 6 H L = U, no further analytic
-- cancellation is needed at the selected point.
clearedFromChain : (l : ℝ) →
  (X * l) ≃ (Y * E.J₁) →
  (N.six * E.H * l) ≃ U → ClearedHyperJet
clearedFromChain l hz hsq =
  P.≃-trans
      (let open P.ℝ-Solver in solve 3 (λ h y j →
        Κ (+ 6 / 1) ⊗ h ⊗ y ⊗ j ⊜ (Κ (+ 6 / 1) ⊗ h) ⊗ (y ⊗ j))
        P.≃-refl E.H Y E.J₁)
      (P.≃-trans (P.*-congˡ (P.≃-symm hz))
        (P.≃-trans
          (let open P.ℝ-Solver in solve 3 (λ h x l →
            (Κ (+ 6 / 1) ⊗ h) ⊗ (x ⊗ l) ⊜ x ⊗ (Κ (+ 6 / 1) ⊗ h ⊗ l))
            P.≃-refl E.H X l)
          (P.*-congˡ hsq)))

-- Literal CM coefficient packet, signed (not absolute value).
K κ p : ℝ
K = Slice.negC
κ = ((Z.-_ (+ 77859659565707)) / 19943834790540897829879824384000) ⋆
p = M.bishopMachinPi * N.r

three : ℝ
three = (+ 3 / 1) ⋆

c : ℝ
c = three - N.six * K * κ

-- Cleared form of the signed transverse two-jet correction:
-- p*(Y U - 3 X^3 - (3 - 6 K kappa) Y^2) = 6 X Y.
-- The actual Möbius disk derivative or original tau jet must
-- produce this equation; no arbitrary sign or local inverse of j.
SignedJet : Set
SignedJet = (p * (Y * U - three * N.cube X - c * N.sq Y)) ≃ (N.six * X * Y)

Cubic : Set
Cubic = N.sq Y ≃ (N.t * N.cube X)

-- Exact scalar normalization, with denominator clearing at the
-- original positive t. 3/t + 3 - 6*K*kappa = -6*A/B.
scalar : (three + c * N.t) * N.B ≃ R.- (N.six * N.A * N.t)
scalar = let open P.ℝ-Solver in solve 0
  ((Κ (+ 3 / 1) ⊕ (Κ (+ 3 / 1) ⊖ Κ (+ 6 / 1) ⊗ Κ Slice.negCQ ⊗
      Κ ((Z.-_ (+ 77859659565707)) / 19943834790540897829879824384000))
       ⊗ Κ (+ 262537412640769728 / 262537412640768000)) ⊗ Κ (+ 545140134 / 1)
    ⊜ ⊝ (Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗
      Κ (+ 262537412640769728 / 262537412640768000))) P.≃-refl

scalarCubic : Cubic →
  (N.B * (three * N.cube X + c * N.sq Y)) ≃ R.- (N.six * N.A * N.sq Y)
scalarCubic hy =
  P.≃-trans (P.*-congˡ (P.+-cong P.≃-refl (P.*-congˡ hy)))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 2 (λ c x →
        Κ (+ 545140134 / 1) ⊗ (Κ (+ 3 / 1) ⊗ x ⊕ c ⊗
          (Κ (+ 262537412640769728 / 262537412640768000) ⊗ x))
        ⊜ ((Κ (+ 3 / 1) ⊕ c ⊗ Κ (+ 262537412640769728 / 262537412640768000))
          ⊗ Κ (+ 545140134 / 1)) ⊗ x) P.≃-refl c (N.cube X))
      (P.≃-trans (P.*-congʳ scalar)
        (P.≃-trans
          (let open P.ℝ-Solver in solve 1 (λ x →
            (⊝ (Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗
             Κ (+ 262537412640769728 / 262537412640768000))) ⊗ x
            ⊜ ⊝ (Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗
             (Κ (+ 262537412640769728 / 262537412640768000) ⊗ x)))
            P.≃-refl (N.cube X))
          (P.-‿cong (P.*-congˡ (P.≃-symm hy))))))

-- Denominator-free signed reduction in both directions. Introduce
-- one intermediate equation, then cancel only positive Y.
jetScaled : Cubic →
  (N.B * (Y * U - three * N.cube X - c * N.sq Y)) ≃ (Y * Jet.V)
jetScaled hy =
  P.≃-trans
    (let open P.ℝ-Solver in solve 4 (λ y u a b →
      Κ (+ 545140134 / 1) ⊗ (y ⊗ u ⊖ a ⊖ b)
        ⊜ Κ (+ 545140134 / 1) ⊗ y ⊗ u ⊖ Κ (+ 545140134 / 1) ⊗ (a ⊕ b))
      P.≃-refl Y U (three * N.cube X) (c * N.sq Y))
    (P.≃-trans (P.+-cong P.≃-refl (P.-‿cong (scalarCubic hy)))
      (let open P.ℝ-Solver in solve 2 (λ y u →
        Κ (+ 545140134 / 1) ⊗ y ⊗ u ⊖ (⊝ (Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗ (y ⊗ y)))
        ⊜ y ⊗ (Κ (+ 545140134 / 1) ⊗ u ⊕ Κ (+ 6 / 1) ⊗ Κ (+ 13591409 / 1) ⊗ y))
        P.≃-refl Y U))

correctionFromSigned : Cubic → SignedJet → Jet.Correction
correctionFromSigned hy h = N.cancelLeft Y Guard.yPositive
  (P.≃-trans
    (let open P.ℝ-Solver in solve 3 (λ y p v →
      y ⊗ (p ⊗ v) ⊜ p ⊗ (y ⊗ v)) P.≃-refl Y p Jet.V)
    (P.≃-trans (P.*-congˡ (P.≃-symm (jetScaled hy)))
      (P.≃-trans
        (let open P.ℝ-Solver in solve 2 (λ p z →
          p ⊗ (Κ (+ 545140134 / 1) ⊗ z) ⊜ Κ (+ 545140134 / 1) ⊗ (p ⊗ z))
          P.≃-refl p (Y * U - three * N.cube X - c * N.sq Y))
        (P.≃-trans (P.*-congˡ h)
          (let open P.ℝ-Solver in solve 2 (λ x y →
            Κ (+ 545140134 / 1) ⊗ (Κ (+ 6 / 1) ⊗ x ⊗ y)
            ⊜ y ⊗ (Κ (+ 6 / 1) ⊗ Κ (+ 545140134 / 1) ⊗ x))
            P.≃-refl X Y)))))

-- Actual root has a native apartness witness already.
CMRoot : Set
CMRoot = Guard.Root.j ≃ Slice.negC

periodFromThree : CMRoot → HyperSquare → ClearedHyperJet → SignedJet → End.NativePeriod
periodFromThree hj hs hflow hjet =
  let hy = Guard.Root.rootToCubic hj in
  Jet.periodFromCubicAndE4Jet Guard.xPositive hs hy
    (flowFromCleared hs hflow) (correctionFromSigned hy hjet)

rawFromThree : CMRoot → HyperSquare → ClearedHyperJet → SignedJet →
  (k : Nat) → Raw.RawCross k
rawFromThree hj hs hflow hjet = Raw.rawFromPeriod (periodFromThree hj hs hflow hjet)

-- Reverse signed correction on the same cubic. Cancellation is of
-- the actual positive integer B, not a chosen complex sign.
import Data.Rational.Unnormalised.Properties as QP

bPositive : R.Positive N.B
bPositive = P.posp⇒posp⋆ (+ 545140134 / 1) (QP.positive⁻¹ (+ 545140134 / 1))

signedFromCorrection : Cubic → Jet.Correction → SignedJet
signedFromCorrection hy hc = N.cancelLeft N.B bPositive
  (P.≃-trans
    (let open P.ℝ-Solver in solve 2 (λ p z →
      Κ (+ 545140134 / 1) ⊗ (p ⊗ z) ⊜ p ⊗ (Κ (+ 545140134 / 1) ⊗ z))
      P.≃-refl p (Y * U - three * N.cube X - c * N.sq Y))
    (P.≃-trans
      (P.≃-refl)
      (P.≃-trans (P.*-congˡ (jetScaled hy))
        (P.≃-trans
          (let open P.ℝ-Solver in solve 3 (λ p y v →
            p ⊗ (y ⊗ v) ⊜ y ⊗ (p ⊗ v)) P.≃-refl p Y Jet.V)
          (P.≃-trans (P.*-congˡ hc)
            (let open P.ℝ-Solver in solve 2 (λ x y →
              y ⊗ (Κ (+ 6 / 1) ⊗ Κ (+ 545140134 / 1) ⊗ x)
              ⊜ Κ (+ 545140134 / 1) ⊗ (Κ (+ 6 / 1) ⊗ x ⊗ y))
              P.≃-refl X Y))))))

-- The three signed derivative relations needed from the actual
-- reciprocal Mobius chart. a=Dj, b=D²j, p=pi_M*sqrt(163).
-- Values must be constructed from the original j, not freely chosen.
FirstQJet : ℝ → Set
FirstQJet a = (X * a) ≃ R.- (K * Y)

SecondQJet : ℝ → Set
SecondQJet b =
  (N.six * N.sq X * b) ≃
    (K * (three * N.cube X + three * N.sq Y - Y * U))

DiskJet : ℝ → ℝ → Set
DiskJet a b = (p * κ * N.sq a) ≃ (p * b - a)

-- Exact polynomial transport from the three actual jet identities.
-- Clearing X² and the signed K leaves the terminal signed relation.
-- In particular no local inverse of j or square-root sign choice.
diskJetCleared : (a b : ℝ) → FirstQJet a → SecondQJet b → DiskJet a b →
  (N.six * p * κ * N.sq (K * Y)) ≃
    (p * (K * (three * N.cube X + three * N.sq Y - Y * U)) +
      N.six * X * (K * Y))
diskJetCleared a b h1 h2 h3 =
  P.≃-trans
    (P.*-congˡ
      (P.≃-symm (P.≃-trans (P.*-cong h1 h1)
        (let open P.ℝ-Solver in solve 1 (λ q → (⊝ q) ⊗ (⊝ q) ⊜ q ⊗ q)
          P.≃-refl (K * Y)))))
    (P.≃-trans
      (let open P.ℝ-Solver in solve 4 (λ p k x a →
        Κ (+ 6 / 1) ⊗ p ⊗ k ⊗ ((x ⊗ a) ⊗ (x ⊗ a))
        ⊜ (Κ (+ 6 / 1) ⊗ (x ⊗ x)) ⊗ (p ⊗ k ⊗ (a ⊗ a)))
        P.≃-refl p κ X a)
      (P.≃-trans (P.*-congˡ h3)
        (P.≃-trans
          (let open P.ℝ-Solver in solve 4 (λ p x a b →
            (Κ (+ 6 / 1) ⊗ (x ⊗ x)) ⊗ (p ⊗ b ⊖ a)
            ⊜ p ⊗ (Κ (+ 6 / 1) ⊗ (x ⊗ x) ⊗ b)
              ⊖ (Κ (+ 6 / 1) ⊗ x ⊗ (x ⊗ a)))
            P.≃-refl p X a b)
          (P.≃-trans
            (P.+-cong (P.*-congˡ h2)
              (P.-‿cong (P.*-congˡ h1)))
            (let open P.ℝ-Solver in solve 4 (λ p k f x →
              p ⊗ f ⊖ (Κ (+ 6 / 1) ⊗ x ⊗ (⊝ k))
              ⊜ p ⊗ f ⊕ Κ (+ 6 / 1) ⊗ x ⊗ k)
              P.≃-refl p (K * Y)
                (K * (three * N.cube X + three * N.sq Y - Y * U)) X)))))

-- Interpret the original negative integer K as a rational constant
-- in the ring solver. Multiplication by its exact reciprocal is
-- justified by the scalar normal form, no real inverse is assumed.
signedFromDiskJet : (a b : ℝ) → FirstQJet a → SecondQJet b → DiskJet a b → SignedJet
signedFromDiskJet a b h1 h2 h3 =
  let
    v = three * N.cube X + three * N.sq Y - Y * U
    ik = ((Z.-_ (+ 1)) / 262537412640768000) ⋆
    open P.ℝ-Solver
    lhs : (ik * (N.six * p * κ * N.sq (K * Y))) ≃
      (N.six * p * κ * K * N.sq Y)
    lhs = solve 3 (λ p k y →
      Κ ((Z.-_ (+ 1)) / 262537412640768000) ⊗
        (Κ (+ 6 / 1) ⊗ p ⊗ k ⊗ ((Κ Slice.negCQ ⊗ y) ⊗ (Κ Slice.negCQ ⊗ y)))
      ⊜ Κ (+ 6 / 1) ⊗ p ⊗ k ⊗ Κ Slice.negCQ ⊗ (y ⊗ y))
      P.≃-refl p κ Y
    rhs : (ik * (p * (K * v) + N.six * X * (K * Y))) ≃
      (p * v + N.six * X * Y)
    rhs = solve 4 (λ p v x y →
      Κ ((Z.-_ (+ 1)) / 262537412640768000) ⊗
        (p ⊗ (Κ Slice.negCQ ⊗ v) ⊕ Κ (+ 6 / 1) ⊗ x ⊗ (Κ Slice.negCQ ⊗ y))
      ⊜ p ⊗ v ⊕ Κ (+ 6 / 1) ⊗ x ⊗ y) P.≃-refl p v X Y
    reduced : (N.six * p * κ * K * N.sq Y) ≃ (p * v + N.six * X * Y)
    reduced = P.≃-trans (P.≃-symm lhs)
      (P.≃-trans (P.*-congˡ (diskJetCleared a b h1 h2 h3)) rhs)
  in P.≃-trans
    (solve 5 (λ p k x y u →
      p ⊗ (y ⊗ u ⊖ Κ (+ 3 / 1) ⊗ (x ⊗ x ⊗ x)
        ⊖ (Κ (+ 3 / 1) ⊖ Κ (+ 6 / 1) ⊗ Κ Slice.negCQ ⊗ k) ⊗ (y ⊗ y))
      ⊜ Κ (+ 6 / 1) ⊗ p ⊗ k ⊗ Κ Slice.negCQ ⊗ (y ⊗ y)
        ⊖ p ⊗ (Κ (+ 3 / 1) ⊗ (x ⊗ x ⊗ x) ⊕ Κ (+ 3 / 1) ⊗ (y ⊗ y) ⊖ y ⊗ u))
      P.≃-refl p κ X Y U)
    (P.≃-trans (P.+-cong reduced P.≃-refl)
      (solve 4 (λ p v x y →
        (p ⊗ v ⊕ Κ (+ 6 / 1) ⊗ x ⊗ y) ⊖ p ⊗ v
        ⊜ Κ (+ 6 / 1) ⊗ x ⊗ y) P.≃-refl p v X Y))
