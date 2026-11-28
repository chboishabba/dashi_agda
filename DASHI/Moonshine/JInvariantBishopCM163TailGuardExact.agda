module DASHI.Moonshine.JInvariantBishopCM163TailGuardExact where

-- SOURCE-WRITTEN, UNCOMPILED. All-index tail bounds for the literal
-- negative-real selected q-series. Keep the first signed term separate.
-- Classical Eisenstein coefficients; original Bishop convergence owners.
open import Agda.Builtin.Nat using (Nat; zero; suc)
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
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
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
baseStep : (n : Nat) → suc (suc n) Nat.≤ Nat._*_ 2 (suc n)
baseStep n = subst₂ Nat._≤_
  (solve 1 (λ n → (con 1 :+ n) :+ con 1 := con 1 :+ (con 1 :+ n)) refl n)
  (solve 1 (λ n → (con 1 :+ n) :+ (con 1 :+ n) := con 2 :* (con 1 :+ n)) refl n)
  (NP.+-mono-≤ NP.≤-refl (s≤s z≤n))

powMono : (a b d : Nat) → a Nat.≤ b → Pow.powNat a d Nat.≤ Pow.powNat b d
powMono a b zero h = NP.≤-refl
powMono a b (suc d) h = NP.*-mono-≤ h (powMono a b d h)

powMul : (a b d : Nat) → Pow.powNat (Nat._*_ a b) d ≡ Nat._*_ (Pow.powNat a d) (Pow.powNat b d)
powMul a b zero = refl
powMul a b (suc d) rewrite powMul a b d =
  solve 4 (λ a b x y → (a :* b) :* (x :* y) := (a :* x) :* (b :* y))
    refl a b (Pow.powNat a d) (Pow.powNat b d)

coeffStep : (d n : Nat) → Pow.powNat 2 d Nat.≤ 64 →
  Pow.powNat (suc (suc n)) d Nat.≤ Nat._*_ 64 (Pow.powNat (suc n) d)
coeffStep d n hd = NP.≤-trans
  (powMono (suc (suc n)) (Nat._*_ 2 (suc n)) d (baseStep n))
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
      (P.≤-respˡ-≃ (P.≃-symm (P.∣-x∣≃∣x∣ {x = t n})) (bound n))))

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
    (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 1
      (λ p → p ⊖ Κ Q.0ℚᵘ ⊜ p) P.≃-refl (partial n))
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


-- Bind the first signed term to the actual q-power constructor. The
-- coefficient at n=0 is exactly sigma_3(1)=sigma_5(1)=1.
first4 : t4 zero ≃ R.- (((+ 240 / 1) ⋆) * CM.radius)
first4 = let open P.ℝ-Solver in solve 1
  (λ r → Κ (+ 240 / 1) ⊗ ((⊝ r) ⊗ Κ Q.1ℚᵘ ⊖ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ)
    ⊜ ⊝ (Κ (+ 240 / 1) ⊗ r)) P.≃-refl CM.radius

first6 : t6 zero ≃ R.- (((+ 504 / 1) ⋆) * CM.radius)
first6 = let open P.ℝ-Solver in solve 1
  (λ r → Κ (+ 504 / 1) ⊗ ((⊝ r) ⊗ Κ Q.1ℚᵘ ⊖ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ)
    ⊜ ⊝ (Κ (+ 504 / 1) ⊗ r)) P.≃-refl CM.radius

gap4 : Four.gap zero ≃ ((+ 16 / 1) ⋆) * CM.radius
gap4 = P.≃-trans (P.*-congˡ (majorantZero Maj.e4Scale 4))
  (let open P.ℝ-Solver in solve 1 (λ r →
    Κ (+ 1 / 15) ⊗ (Κ (+ 240 / 1) ⊗ r) ⊜ Κ (+ 16 / 1) ⊗ r)
    P.≃-refl CM.radius)

gap6 : Six.gap zero ≃ ((+ 168 / 5) ⋆) * CM.radius
gap6 = P.≃-trans (P.*-congˡ (majorantZero Maj.e6Scale 6))
  (let open P.ℝ-Solver in solve 1 (λ r →
    Κ (+ 1 / 15) ⊗ (Κ (+ 504 / 1) ⊗ r) ⊜ Κ (+ 168 / 5) ⊗ r)
    P.≃-refl CM.radius)

X Y : ℝ
X = CM.Selected.X
Y = CM.Selected.Y

xLowerRadius : R.1ℝ - (((+ 256 / 1) ⋆) * CM.radius) ≤ X
xLowerRadius = P.≤-respˡ-≃
  (P.≃-trans (P.+-cong P.≃-refl (P.+-cong first4 (P.-‿cong gap4)))
    (let open P.ℝ-Solver in solve 1 (λ r →
      Κ Q.1ℚᵘ ⊕ ((⊝ (Κ (+ 240 / 1) ⊗ r)) ⊖ Κ (+ 16 / 1) ⊗ r)
        ⊜ Κ Q.1ℚᵘ ⊖ Κ (+ 256 / 1) ⊗ r) P.≃-refl CM.radius))
  (P.+-monoʳ-≤ R.1ℝ (proj₁ tail4Bounds))

xUpperRadius : X ≤ R.1ℝ - (((+ 224 / 1) ⋆) * CM.radius)
xUpperRadius = P.≤-respʳ-≃
  (P.≃-trans (P.+-cong P.≃-refl (P.+-cong first4 gap4))
    (let open P.ℝ-Solver in solve 1 (λ r →
      Κ Q.1ℚᵘ ⊕ ((⊝ (Κ (+ 240 / 1) ⊗ r)) ⊕ Κ (+ 16 / 1) ⊗ r)
        ⊜ Κ Q.1ℚᵘ ⊖ Κ (+ 224 / 1) ⊗ r) P.≃-refl CM.radius))
  (P.+-monoʳ-≤ R.1ℝ (proj₂ tail4Bounds))

yLowerRadius : R.1ℝ + (((+ 2352 / 5) ⋆) * CM.radius) ≤ Y
yLowerRadius = P.≤-respˡ-≃
  (P.≃-trans (P.+-cong P.≃-refl (P.-‿cong (P.+-cong first6 gap6)))
    (let open P.ℝ-Solver in solve 1 (λ r →
      Κ Q.1ℚᵘ ⊖ ((⊝ (Κ (+ 504 / 1) ⊗ r)) ⊕ Κ (+ 168 / 5) ⊗ r)
        ⊜ Κ Q.1ℚᵘ ⊕ Κ (+ 2352 / 5) ⊗ r) P.≃-refl CM.radius))
  (P.+-monoʳ-≤ R.1ℝ (P.neg-mono-≤ (proj₂ tail6Bounds)))

xLower : ((+ 3 / 4) ⋆) ≤ X
xLower = P.≤-trans
  (P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 0
      (Κ Q.1ℚᵘ ⊖ (Κ (+ 256 / 1) ⊗ Κ (+ 1 / 1024)) ⊜ Κ (+ 3 / 4))
      P.≃-refl)
    (P.+-monoʳ-≤ R.1ℝ (P.neg-mono-≤
      (P.*-monoˡ-≤-nonNeg (P.<⇒≤ G.radiusSmall)
        (G.ratNN (+ 256 / 1) (QP.nonNegative⁻¹ (+ 256 / 1)))))))
  xLowerRadius

xPositive : R.Positive X
xPositive = P.0<x⇒posx
  (P.<-≤-trans (G.ratLt Q.0ℚᵘ (+ 3 / 4) (QP.positive⁻¹ (+ 3 / 4))) xLower)

positiveScale : (p : Q.ℚᵘ) → Q.0ℚᵘ Q.< p →
  R.0ℝ < (p ⋆) * CM.radius
positiveScale p hp = P.posx⇒0<x (P.posx,y⇒posx*y
  (P.0<x⇒posx (G.ratLt Q.0ℚᵘ p hp)) (P.0<x⇒posx G.radiusPositive))

xBelowOne : X < R.1ℝ
xBelowOne = P.≤-<-trans xUpperRadius
  (P.<-respʳ-≃ (let open P.ℝ-Solver in solve 0
      (Κ Q.1ℚᵘ ⊖ Κ Q.0ℚᵘ ⊜ Κ Q.1ℚᵘ) P.≃-refl)
    (P.+-monoʳ-< R.1ℝ (P.neg-mono-<
      (positiveScale (+ 224 / 1) (QP.positive⁻¹ (+ 224 / 1))))))

oneBelowY : R.1ℝ < Y
oneBelowY = P.<-≤-trans
  (P.<-respˡ-≃ (P.+-identityʳ R.1ℝ)
    (P.+-monoʳ-< R.1ℝ
      (positiveScale (+ 2352 / 5) (QP.positive⁻¹ (+ 2352 / 5)))))
  yLowerRadius

xNN : R.NonNegative X
xNN = P.pos⇒nonNeg xPositive

yPositive : R.Positive Y
yPositive = P.0<x⇒posx (P.<-trans
  (G.ratLt Q.0ℚᵘ Q.1ℚᵘ (QP.positive⁻¹ Q.1ℚᵘ)) oneBelowY)

xSquareBelowOne : X * X ≤ R.1ℝ
xSquareBelowOne = P.≤-trans
  (P.≤-respʳ-≃ (P.*-identityˡ X) (P.*-monoʳ-≤-nonNeg (P.<⇒≤ xBelowOne) xNN))
  (P.<⇒≤ xBelowOne)

xCubeBelowOne : (X * X) * X ≤ R.1ℝ
xCubeBelowOne = P.≤-trans
  (P.≤-respʳ-≃ (P.*-identityˡ X) (P.*-monoʳ-≤-nonNeg xSquareBelowOne xNN))
  (P.<⇒≤ xBelowOne)

oneBelowYSquare : R.1ℝ < Y * Y
oneBelowYSquare = P.<-trans oneBelowY
  (P.<-respˡ-≃ (P.*-identityˡ Y) (P.*-monoˡ-<-pos yPositive oneBelowY))

-- Guard the literal normalized discriminant (not a substituted j).
negativeDelta : CM.Selected.d < R.0ℝ
negativeDelta =
  let
    h = P.≤-<-trans xCubeBelowOne oneBelowYSquare
    diff = P.<-respʳ-≃
      (let open P.ℝ-Solver in solve 1 (λ y → y ⊖ y ⊜ Κ Q.0ℚᵘ)
        P.≃-refl (Y * Y))
      (P.+-monoˡ-< (R.- (Y * Y)) h)
    scaled = P.*-monoʳ-<-pos
      (P.posp⇒posp⋆ (+ 1 / 1728) (QP.positive⁻¹ (+ 1 / 1728))) diff
  in P.<-respˡ-≃ (P.≃-symm CM.Selected.deltaRe)
    (P.<-respʳ-≃ (P.*-zeroʳ ((+ 1 / 1728) ⋆)) scaled)

module Root = CM.Selected.AtNegativeDelta negativeDelta

-- Same original absolute streams used by the disk completion.
-- Their L1 budgets are needed for the formal composition evaluation.
abs4 abs6 : Nat → ℝ
abs4 n = R.∣ t4 n ∣
abs6 n = R.∣ t6 n ∣

absAbs : (x : ℝ) → R.∣ R.∣ x ∣ ∣ ≃ R.∣ x ∣
absAbs x = P.nonNegx⇒∣x∣≃x (P.nonNeg∣x∣ x)

module AbsFour = Telescope abs4 (majorant Maj.e4Scale 4)
  (majorantNN Maj.e4ScaleNonnegative 4)
  (λ n → majorantStep Maj.e4ScaleNonnegative 4 n (from-yes (16 NP.≤? 64)))
  (λ n → P.≤-respˡ-≃ (P.≃-symm (absAbs (t4 n)))
    (E.e4RealTermBound CM.q unit envelope n))

module AbsSix = Telescope abs6 (majorant Maj.e6Scale 6)
  (majorantNN Maj.e6ScaleNonnegative 6)
  (λ n → majorantStep Maj.e6ScaleNonnegative 6 n NP.≤-refl)
  (λ n → P.≤-respˡ-≃ (P.≃-symm (absAbs (t6 n)))
    (E.e6RealTermBound CM.q unit envelope n))

abs4Cauchy : S._isConvergent (S.SeriesOf abs4)
abs4Cauchy = C.realAbsolute (Disk.e4AbsoluteConvergence Actual.completion)

abs6Cauchy : S._isConvergent (S.SeriesOf abs6)
abs6Cauchy = C.realAbsolute (Disk.e6AbsoluteConvergence Actual.completion)

l1X l1Y : ℝ
l1X = S.lim abs4Cauchy
l1Y = S.lim abs6Cauchy

absFirstBound : (t m : Nat → ℝ) → R.∣ t zero ∣ ≤ m zero →
  R.∣ t zero ∣ + fifteenth * m zero ≤ m zero + fifteenth * m zero
absFirstBound t m h = P.+-monoˡ-≤ (fifteenth * m zero) h

l1XRadius : l1X ≤ ((+ 256 / 1) ⋆) * CM.radius
l1XRadius = P.≤-trans (proj₂ (AbsFour.limitBounds l1X (proj₂ abs4Cauchy)))
  (P.≤-respʳ-≃
    (P.≃-trans (P.+-cong (majorantZero Maj.e4Scale 4) gap4)
      (let open P.ℝ-Solver in solve 1 (λ r →
        Κ (+ 240 / 1) ⊗ r ⊕ Κ (+ 16 / 1) ⊗ r ⊜ Κ (+ 256 / 1) ⊗ r)
        P.≃-refl CM.radius))
    (absFirstBound t4 (majorant Maj.e4Scale 4)
      (E.e4RealTermBound CM.q unit envelope zero)))

l1YRadius : l1Y ≤ ((+ 2688 / 5) ⋆) * CM.radius
l1YRadius = P.≤-trans (proj₂ (AbsSix.limitBounds l1Y (proj₂ abs6Cauchy)))
  (P.≤-respʳ-≃
    (P.≃-trans (P.+-cong (majorantZero Maj.e6Scale 6) gap6)
      (let open P.ℝ-Solver in solve 1 (λ r →
        Κ (+ 504 / 1) ⊗ r ⊕ Κ (+ 168 / 5) ⊗ r ⊜ Κ (+ 2688 / 5) ⊗ r)
        P.≃-refl CM.radius))
    (absFirstBound t6 (majorant Maj.e6Scale 6)
      (E.e6RealTermBound CM.q unit envelope zero)))

l1XSmall : l1X < ((+ 1 / 25) ⋆)
l1XSmall = P.≤-<-trans l1XRadius
  (P.<-trans
    (P.<-respʳ-≃ (let open P.ℝ-Solver in solve 0
      (Κ (+ 256 / 1) ⊗ Κ (+ 1 / 7000) ⊜ Κ (+ 32 / 875)) P.≃-refl)
      (P.*-monoʳ-<-pos
        (P.posp⇒posp⋆ (+ 256 / 1) (QP.positive⁻¹ (+ 256 / 1))) G.radiusCompositionSmall))
    (G.ratLt (+ 32 / 875) (+ 1 / 25) (from-yes ((+ 32 / 875) QP.<? (+ 1 / 25)))))

l1YSmall : l1Y < ((+ 2 / 25) ⋆)
l1YSmall = P.≤-<-trans l1YRadius
  (P.<-trans
    (P.<-respʳ-≃ (let open P.ℝ-Solver in solve 0
      (Κ (+ 2688 / 5) ⊗ Κ (+ 1 / 7000) ⊜ Κ (+ 48 / 625)) P.≃-refl)
      (P.*-monoʳ-<-pos
        (P.posp⇒posp⋆ (+ 2688 / 5) (QP.positive⁻¹ (+ 2688 / 5))) G.radiusCompositionSmall))
    (G.ratLt (+ 48 / 625) (+ 2 / 25) (from-yes ((+ 48 / 625) QP.<? (+ 2 / 25)))))

-- Exact scalar budget for the yet-unattached weighted Cauchy algebra:
-- ((1+1/25)^3+(1+2/25)^2-2)/(1-1/25)^3 = 1517/4608 < 1/3.
-- The algebra's norm-submultiplicativity and composition evaluation
-- must still be proved; the scalar budget is not itself that weld.
compositionBudget : (+ 1517 / 4608) Q.< (+ 1 / 3)
compositionBudget = from-yes ((+ 1517 / 4608) QP.<? (+ 1 / 3))

compositionBudgetCleared :
  ((((+ 26 / 25) Q.* (+ 26 / 25)) Q.* (+ 26 / 25)) Q.+ ((+ 27 / 25) Q.* (+ 27 / 25))
    Q.- (+ 2 / 1)) Q.≃
  ((+ 1517 / 4608) Q.* (((+ 24 / 25) Q.* (+ 24 / 25)) Q.* (+ 24 / 25)))
compositionBudgetCleared = Q.*≡* refl
