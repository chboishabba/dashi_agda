module DASHI.Moonshine.JInvariantBishopCM163TailGuardExact where

-- SOURCE-WRITTEN, UNCOMPILED. All-index tail bounds for the literal
-- negative-real selected q-series. Keep the first signed term separate.
-- Classical Eisenstein coefficients; original Bishop convergence owners.
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Nat.Base using (s≤s; z≤n)
import Data.Nat.Base as Nat
import Data.Nat.Properties as NP
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver using (solve; _:+_; _:*_; con; _:=_)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; subst₂)
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_×_; _,_)
import Real as R
open R using (ℝ; _≃_; _*_; _+_; _-_; _⋆; _≤_; _<_)
import RealProperties as P
import Sequence as S
import DASHI.Mathematics.NumberTheory.FiniteDivisorPowerSumExact as Pow
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Foundations.BishopNatEmbeddingMonotoneExact as NM
import DASHI.Foundations.BishopNatEmbeddingPowerExact as NB
import DASHI.Analysis.BishopPolynomialGeometricSeriesConvergenceExact as Poly
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Maj
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact as G

-- Polynomial coefficient growth (n+2)^d <= 2^d*(n+1)^d.
baseStep : (n : Nat) → suc (suc n) Nat.≤ 2 * suc n
baseStep n = subst₂ Nat._≤_
  (solve 1 (λ n → (con 1 :+ n) :+ con 1 := con 1 :+ (con 1 :+ n)) refl n)
  (solve 1 (λ n → (con 1 :+ n) :+ (con 1 :+ n) := con 2 :* (con 1 :+ n)) refl n)
  (NP.+-mono-≤ NP.≤-refl (s≤s z≤n))

powMono : (a b d : Nat) → a Nat.≤ b → Pow.powNat a d Nat.≤ Pow.powNat b d
powMono a b zero h = NP.≤-refl
powMono a b (suc d) h = NP.*-mono-≤ h (powMono a b d h)

powMul : (a b d : Nat) → Pow.powNat (a * b) d ≡ Pow.powNat a d * Pow.powNat b d
powMul a b zero = refl
powMul a b (suc d) rewrite powMul a b d =
  solve 4 (λ a b x y → (a :* b) :* (x :* y) := (a :* x) :* (b :* y))
    refl a b (Pow.powNat a d) (Pow.powNat b d)

coeffStep : (d n : Nat) → Pow.powNat 2 d Nat.≤ 64 →
  Pow.powNat (suc (suc n)) d Nat.≤ 64 * Pow.powNat (suc n) d
coeffStep d n hd = NP.≤-trans
  (powMono (suc (suc n)) (2 * suc n) d (baseStep n))
  (NP.≤-trans (NP.≤-reflexive (powMul 2 (suc n) d))
    (NP.*-mono-≤ hd NP.≤-refl))

embeddedCoeffStep : (d n : Nat) → Pow.powNat 2 d Nat.≤ 64 →
  R.pow (NR.natReal (suc (suc n))) d ≤
  ((+ 64 / 1) ⋆) * R.pow (NR.natReal (suc n)) d
embeddedCoeffStep d n hd = P.≤-respˡ-≃ (NB.natRealPowNat (suc (suc n)) d)
  (P.≤-respʳ-≃
    (P.≃-trans (NR.natRealMul 64 (Pow.powNat (suc n) d))
      (P.*-congˡ (NB.natRealPowNat (suc n) d)))
    (NM.natRealMonotone (coeffStep d n hd)))

rNN : R.NonNegative CM.radius
rNN = P.0≤x⇒nonNegx (P.<⇒≤ G.radiusPositive)

ratio : ℝ
ratio = (+ 1 / 16) ⋆

fifteenth : ℝ
fifteenth = (+ 1 / 15) ⋆

ratioNN : R.NonNegative ratio
ratioNN = G.ratNN (+ 1 / 16) (QP.nonNegative⁻¹ (+ 1 / 16))

fifteenthNN : R.NonNegative fifteenth
fifteenthNN = G.ratNN (+ 1 / 15) (QP.nonNegative⁻¹ (+ 1 / 15))

scaledRadius : ((+ 64 / 1) ⋆) * CM.radius ≤ ratio
scaledRadius = P.≤-respʳ-≃
  (let open P.ℝ-Solver in solve 0
    (Κ (+ 64 / 1) ⊗ Κ (+ 1 / 1024) ⊜ Κ (+ 1 / 16)) P.≃-refl)
  (P.*-monoˡ-≤-nonNeg (P.<⇒≤ G.radiusSmall)
    (G.ratNN (+ 64 / 1) (QP.nonNegative⁻¹ (+ 64 / 1))))

majorant : ℝ → Nat → Nat → ℝ
majorant scale d = Poly.shiftedScaledPolynomialGeometricTerm scale CM.radius d

majorantNN : ∀ {scale} → R.NonNegative scale → (d n : Nat) →
  R.NonNegative (majorant scale d n)
majorantNN ps d n = Poly.shiftedScaledPolynomialGeometricTermNonnegative
  (P.<⇒≤ G.radiusPositive) ps d n

-- Use the actual polynomial-geometric majorant, not a new series.
majorantStep : ∀ {scale} → R.NonNegative scale → (d n : Nat) →
  Pow.powNat 2 d Nat.≤ 64 →
  majorant scale d (suc n) ≤ ratio * majorant scale d n
majorantStep {scale} ps d n hd =
  let
    p = R.pow (NR.natReal (suc n)) d
    r = R.pow CM.radius (suc n)
    raw = P.*-monoˡ-≤-nonNeg
      (P.*-monoʳ-≤-nonNeg (embeddedCoeffStep d n hd)
        (S.nonNegx⇒nonNegxⁿ (suc (suc n)) rNN)) ps
    open P.ℝ-Solver
  in P.≤-trans
    (P.≤-respʳ-≃
      (solve 4 (λ s p r q →
        s ⊗ ((Κ (+ 64 / 1) ⊗ p) ⊗ (r ⊗ q))
          ⊜ (Κ (+ 64 / 1) ⊗ q) ⊗ (s ⊗ (p ⊗ r)))
        P.≃-refl scale p r CM.radius) raw)
    (P.*-monoʳ-≤-nonNeg scaledRadius (majorantNN ps d n))

majorantZero : (scale : ℝ) (d : Nat) →
  majorant scale d zero ≃ scale * CM.radius
majorantZero scale d =
  P.*-congˡ (P.≃-trans (P.*-congʳ (onePower d))
    (let open P.ℝ-Solver in solve 1 (λ r →
      Κ Q.1ℚᵘ ⊗ (Κ Q.1ℚᵘ ⊗ r) ⊜ r) P.≃-refl CM.radius))
  where
  onePower : (k : Nat) → R.pow (NR.natReal 1) k ≃ R.1ℝ
  onePower zero = P.≃-refl
  onePower (suc k) = P.≃-trans (P.*-congʳ (onePower k)) (P.*-identityʳ R.1ℝ)

-- A finite signed telescope: retain the current majorant as a residual
-- budget. If m[n+1] <= m[n]/16, then the signed partial sum after its
-- first term is trapped within m[0]/15, uniformly in the cutoff.
module Telescope (t m : Nat → ℝ)
  (mNN : (n : Nat) → R.NonNegative (m n))
  (step : (n : Nat) → m (suc n) ≤ ratio * m n)
  (bound : (n : Nat) → R.∣ t n ∣ ≤ m n) where

  partial : Nat → ℝ
  partial n = S.SeriesOf t (suc n)

  gap : Nat → ℝ
  gap n = fifteenth * m n

  gapNN : (n : Nat) → R.NonNegative (gap n)
  gapNN n = P.nonNegx,y⇒nonNegx*y fifteenthNN (mNN n)

  upperTerm : (n : Nat) → t n ≤ m n
  upperTerm n = P.≤-trans (P.x≤∣x∣ (t n)) (bound n)

  lowerTerm : (n : Nat) → R.- (m n) ≤ t n
  lowerTerm n = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1 (λ x → ⊝ (⊝ x) ⊜ x) P.≃-refl (t n))
    (P.neg-mono-≤ (P.≤-trans (P.x≤∣x∣ (R.- (t n)))
      (P.≤-respˡ-≃ (P.≃-symm (P.∣-x∣≃∣x∣ (t n))) (bound n))))

  pay : (n : Nat) → m (suc n) + gap (suc n) ≤ gap n
  pay n = let open P.ℝ-Solver in
    P.≤-respˡ-≃
      (solve 1 (λ x → Κ (+ 16 / 15) ⊗ x ⊜ x ⊕ Κ (+ 1 / 15) ⊗ x)
        P.≃-refl (m (suc n)))
      (P.≤-respʳ-≃
        (solve 1 (λ x → Κ (+ 16 / 15) ⊗ (Κ (+ 1 / 16) ⊗ x)
          ⊜ Κ (+ 1 / 15) ⊗ x) P.≃-refl (m n))
        (P.*-monoˡ-≤-nonNeg (step n)
          (G.ratNN (+ 16 / 15) (QP.nonNegative⁻¹ (+ 16 / 15)))))

  upperInvariant : (n : Nat) → partial n + gap n ≤ t zero + gap zero
  upperInvariant zero = P.≤-reflexive (P.+-cong (P.+-identityˡ (t zero)) P.≃-refl)
  upperInvariant (suc n) = let open P.ℝ-Solver in
    P.≤-trans
      (P.≤-respˡ-≃
        (solve 3 (λ p t g → p ⊕ (t ⊕ g) ⊜ (p ⊕ t) ⊕ g)
          P.≃-refl (partial n) (t (suc n)) (gap (suc n)))
        (P.+-monoʳ-≤ (partial n)
          (P.≤-trans (P.+-monoˡ-≤ (gap (suc n)) (upperTerm (suc n))) (pay n))))
      (upperInvariant n)

  lowerInvariant : (n : Nat) → t zero - gap zero ≤ partial n - gap n
  lowerInvariant zero = P.≤-reflexive
    (P.+-cong (P.≃-symm (P.+-identityˡ (t zero))) P.≃-refl)
  lowerInvariant (suc n) = let open P.ℝ-Solver in
    P.≤-trans (lowerInvariant n)
      (P.≤-respʳ-≃
        (solve 3 (λ p t g → p ⊕ (t ⊖ g) ⊜ (p ⊕ t) ⊖ g)
          P.≃-refl (partial n) (t (suc n)) (gap (suc n)))
        (P.+-monoʳ-≤ (partial n)
          (P.≤-trans
            (P.≤-respʳ-≃
              (solve 2 (λ m g → ⊝ (m ⊕ g) ⊜ (⊝ m) ⊖ g)
                P.≃-refl (m (suc n)) (gap (suc n)))
              (P.neg-mono-≤ (pay n)))
            (P.+-monoˡ-≤ (R.- (gap (suc n))) (lowerTerm (suc n))))))

  partialUpper : (n : Nat) → partial n ≤ t zero + gap zero
  partialUpper n = P.≤-trans (S.0≤x⇒y≤y+x (partial n) (P.nonNegx⇒0≤x (gapNN n)))
    (upperInvariant n)

  partialLower : (n : Nat) → t zero - gap zero ≤ partial n
  partialLower n = P.≤-trans (lowerInvariant n)
    (P.≤-respʳ-≃ (P.+-identityʳ (partial n))
      (P.+-monoʳ-≤ (partial n) (P.neg-mono-≤ (P.nonNegx⇒0≤x (gapNN n)))))

  partialConverges : (v : ℝ) → S._ConvergesTo_ (S.SeriesOf t) v → S._isConvergent partial
  partialConverges v h = v ,
    S.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y (S.shift-is-subsequence (S.SeriesOf t) 1) (v , h)

  constantConverges : (v : ℝ) → S._isConvergent (λ _ → v)
  constantConverges v = v , S.xₙ≃c⇒xₙ→c (λ {(suc n) → P.≃-refl})

  limitBounds : (v : ℝ) → S._ConvergesTo_ (S.SeriesOf t) v →
    (t zero - gap zero ≤ v) × (v ≤ t zero + gap zero)
  limitBounds v h =
    S.xₙ≤yₙ⇒limxₙ≤limyₙ partialLower (constantConverges (t zero - gap zero))
      (partialConverges v h) ,
    S.xₙ≤yₙ⇒limxₙ≤limyₙ partialUpper (partialConverges v h)
      (constantConverges (t zero + gap zero))

unit = Disk.unitInterval CM.input
envelope = Disk.powerEnvelope CM.input
module Actual = CM.Selected.Actual

t4 t6 : Nat → ℝ
t4 n = C.re (E.e4BishopTerm CM.q n)
t6 n = C.re (E.e6BishopUnsignedTerm CM.q n)

module Four = Telescope t4 (majorant Maj.e4Scale 4)
  (majorantNN Maj.e4ScaleNonnegative 4)
  (λ n → majorantStep Maj.e4ScaleNonnegative 4 n (from-yes (16 NP.≤? 64)))
  (E.e4RealTermBound CM.q unit envelope)

module Six = Telescope t6 (majorant Maj.e6Scale 6)
  (majorantNN Maj.e6ScaleNonnegative 6)
  (λ n → majorantStep Maj.e6ScaleNonnegative 6 n NP.≤-refl)
  (E.e6RealTermBound CM.q unit envelope)

tail4 tail6 : ℝ
tail4 = C.re (E.e4BishopTailLimit CM.q unit envelope)
tail6 = C.re (E.e6BishopUnsignedTailLimit CM.q unit envelope)

tail4Bounds : (t4 zero - Four.gap zero ≤ tail4) × (tail4 ≤ t4 zero + Four.gap zero)
tail4Bounds = Four.limitBounds tail4 (C.realConverges (Disk.e4Converges Actual.completion))

tail6Bounds : (t6 zero - Six.gap zero ≤ tail6) × (tail6 ≤ t6 zero + Six.gap zero)
tail6Bounds = Six.limitBounds tail6 (C.realConverges (Disk.e6Converges Actual.completion))
