module DASHI.Moonshine.JInvariantBishopCM163SharpRootEnclosureExact where

-- Source-written. A half-unit enclosure of the original guarded j:
-- bound the actual signed E4/E6 tails after their first two terms,
-- then clear the negative discriminant using exact rational endpoints.
-- No j integrality, modularity or equality with K is used.
open import Agda.Builtin.Nat using (Nat; zero; suc) renaming (_+_ to _+N_)
open import Data.Nat.Properties using (≤-refl; _≤?_)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_)
import Data.Rational.Unnormalised as Q
import Data.Rational.Unnormalised.Properties as QP
open import Data.Product.Base using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary.Decidable.Core using (from-yes)
import Real as R
open R using (ℝ; _≃_; _≤_; _*_; _+_; _-_; _⋆; ∣_∣)
import RealProperties as P
import Sequence as S
import DASHI.Moonshine.JInvariantBishopCM163SharpRadiusExact as Rad
open Rad using (Band; rat≤; nn; cancelOrder; rL; rU)
import DASHI.Moonshine.JInvariantBishopCM163TailGuardExact as G
import DASHI.Moonshine.JInvariantBishopCM163SelectedDiskExact as CM
import DASHI.Moonshine.JInvariantBishopCM163HalfUnitIsolationExact as Iso
import DASHI.Moonshine.JInvariantBishopCM163RadiusGuardExact as RG
import DASHI.Moonshine.JInvariantBishopCM163NativeJetReductionExact as J
import DASHI.Moonshine.JInvariantEisensteinBishopSetoidSeriesExact as E
import DASHI.Moonshine.JInvariantEisensteinBishopMajorantSeriesExact as Maj
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Disk
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Foundations.BishopChudnovskySignedPeriodNormalizationExact as N
import DASHI.Foundations.BishopNonnegativeSquareReflectionExact as Reflect
import DASHI.Foundations.BishopSquareNonnegativeExact as Sq

-- Exact interval operations used by the actual polynomial observations.
addBand : ∀ {l u a b : Q.ℚᵘ} {x y : ℝ} →
  Band l x u → Band a y b → Band (l Q.+ a) (x + y) (u Q.+ b)
addBand {l} {u} {a} {b} (hl , hu) (ha , hb) =
  P.≤-respˡ-≃ (P.≃-symm (P.⋆-distrib-+ l a)) (P.+-mono-≤ hl ha) ,
  P.≤-respʳ-≃ (P.≃-symm (P.⋆-distrib-+ u b)) (P.+-mono-≤ hu hb)

negBand : ∀ {l u : Q.ℚᵘ} {x : ℝ} → Band l x u → Band (Q.- u) (R.- x) (Q.- l)
negBand {l} {u} (hl , hu) =
  P.≤-respˡ-≃ (P.≃-symm (P.⋆-distrib-neg u)) (P.neg-mono-≤ hu) ,
  P.≤-respʳ-≃ (P.≃-symm (P.⋆-distrib-neg l)) (P.neg-mono-≤ hl)

subBand : ∀ {l u a b : Q.ℚᵘ} {x y : ℝ} →
  Band l x u → Band a y b → Band (l Q.- b) (x - y) (u Q.- a)
subBand h k = addBand h (negBand k)

constant : (q : Q.ℚᵘ) → Band q (q ⋆) q
constant q = P.≤-refl , P.≤-refl

positiveMul : ∀ {l u a b : Q.ℚᵘ} {x y : ℝ} →
  Q.0ℚᵘ Q.≤ l → Q.0ℚᵘ Q.≤ a →
  Band l x u → Band a y b → Band (l Q.* a) (x * y) (u Q.* b)
positiveMul {l} {u} {a} {b} h k (hl , hu) (ha , hb) =
  let xNN = P.0≤x⇒nonNegx (P.≤-trans (rat≤ Q.0ℚᵘ l h) hl)
      yNN = P.0≤x⇒nonNegx (P.≤-trans (rat≤ Q.0ℚᵘ a k) ha)
  in P.≤-respˡ-≃ (P.≃-symm (P.⋆-distrib-* l a))
       (P.*-mono-≤ (nn l h) (nn a k) hl ha) ,
     P.≤-respʳ-≃ (P.≃-symm (P.⋆-distrib-* u b))
       (P.*-mono-≤ xNN yNN hu hb)

widen : ∀ {l u a b : Q.ℚᵘ} {x : ℝ} →
  a Q.≤ l → u Q.≤ b → Band l x u → Band a x b
widen {l} {u} {a} {b} h k (hl , hu) =
  P.≤-trans (rat≤ a l h) hl , P.≤-trans hu (rat≤ u b k)

transport : ∀ {l u : Q.ℚᵘ} {x y : ℝ} → x ≃ y → Band l x u → Band l y u
transport eq (hl , hu) = P.≤-respʳ-≃ eq hl , P.≤-respˡ-≃ eq hu

-- The original majorant has ratio <=1/16. At cutoff 2 the
-- remaining budget is (16/15) m[2], including the first omitted term.
module Tail2 (t m : Nat → ℝ)
  (mNN : (n : Nat) → R.NonNegative (m n))
  (step : (n : Nat) → m (suc n) ≤ G.ratio * m n)
  (bound : (n : Nat) → ∣ t n ∣ ≤ m n) where

  ps = S.SeriesOf t
  budget : Nat → ℝ
  budget n = ((+ 16 / 15) ⋆) * m (n +N 2)

  pay : (n : Nat) → m (n +N 2) + budget (suc n) ≤ budget n
  pay n = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1 (λ m → m ⊕ Κ (+ 16 / 15) ⊗ (Κ (+ 1 / 16) ⊗ m) ⊜ Κ (+ 16 / 15) ⊗ m)
      P.≃-refl (m (n +N 2)))
    (P.+-monoʳ-≤ (m (n +N 2))
      (P.*-monoˡ-≤-nonNeg (step (n +N 2)) (nn (+ 16 / 15) (QP.nonNegative⁻¹ (+ 16 / 15)))))

  termU : (n : Nat) → t n ≤ m n
  termU n = P.≤-trans (P.x≤∣x∣ {x = t n}) (bound n)

  termL : (n : Nat) → R.- m n ≤ t n
  termL n = P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 1 (λ x → ⊝ (⊝ x) ⊜ x) P.≃-refl (t n))
    (P.neg-mono-≤ (P.≤-trans (P.x≤∣x∣ {x = R.- t n})
      (P.≤-respˡ-≃ (P.≃-symm P.∣-x∣≃∣x∣) (bound n))))

  upperInvariant : (n : Nat) → ps (n +N 2) + budget n ≤ ps 2 + budget zero
  upperInvariant zero = P.≤-refl
  upperInvariant (suc n) = P.≤-trans
    (P.≤-respˡ-≃ (P.≃-symm (P.+-assoc (ps (n +N 2)) (t (n +N 2)) (budget (suc n))))
      (P.+-monoʳ-≤ (ps (n +N 2))
        (P.≤-trans (P.+-monoˡ-≤ (budget (suc n)) (termU (n +N 2))) (pay n))))
    (upperInvariant n)

  lowerInvariant : (n : Nat) → ps 2 - budget zero ≤ ps (n +N 2) - budget n
  lowerInvariant zero = P.≤-refl
  lowerInvariant (suc n) = P.≤-trans (lowerInvariant n)
    (P.≤-respʳ-≃
      (let open P.ℝ-Solver in solve 3 (λ p t g → p ⊕ (t ⊖ g) ⊜ (p ⊕ t) ⊖ g)
        P.≃-refl (ps (n +N 2)) (t (n +N 2)) (budget (suc n)))
      (P.+-monoʳ-≤ (ps (n +N 2))
        (P.≤-trans
          (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 2 (λ m g → ⊝ (m ⊕ g) ⊜ (⊝ m) ⊖ g)
            P.≃-refl (m (n +N 2)) (budget (suc n))) (P.neg-mono-≤ (pay n)))
          (P.+-monoˡ-≤ (R.- budget (suc n)) (termL (n +N 2))))))

  bNN : (n : Nat) → R.NonNegative (budget n)
  bNN n = P.nonNegx,y⇒nonNegx*y (nn (+ 16 / 15) (QP.nonNegative⁻¹ (+ 16 / 15))) (mNN (n +N 2))

  upper : (n : Nat) → ps (n +N 2) ≤ ps 2 + budget zero
  upper n = P.≤-trans (S.0≤x⇒y≤y+x (ps (n +N 2)) (P.nonNegx⇒0≤x (bNN n))) (upperInvariant n)

  lower : (n : Nat) → ps 2 - budget zero ≤ ps (n +N 2)
  lower n = P.≤-trans (lowerInvariant n)
    (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 1 (λ p → p ⊖ Κ Q.0ℚᵘ ⊜ p)
      P.≃-refl (ps (n +N 2)))
      (P.+-monoʳ-≤ (ps (n +N 2)) (P.neg-mono-≤ (P.nonNegx⇒0≤x (bNN n)))))

  limits : (v : ℝ) → S._ConvergesTo_ ps v →
    (ps 2 - budget zero ≤ v) × (v ≤ ps 2 + budget zero)
  limits v h =
    let shifted = v , S.fast-xₙ⊆yₙ∧yₙ→y⇒xₙ→y (S.shift-is-subsequence ps 2) (v , h)
    in S.xₙ≤yₙ⇒limxₙ≤limyₙ lower (G.Four.constantConverges (ps 2 - budget zero)) shifted ,
       S.xₙ≤yₙ⇒limxₙ≤limyₙ upper shifted (G.Four.constantConverges (ps 2 + budget zero))

module Four = Tail2 G.t4 (G.majorant Maj.e4Scale 4)
  (G.majorantNN Maj.e4ScaleNonnegative 4)
  (λ n → G.majorantStep Maj.e4ScaleNonnegative 4 n (from-yes (16 ≤? 64)))
  (E.e4RealTermBound CM.q G.unit G.envelope)
module Six = Tail2 G.t6 (G.majorant Maj.e6Scale 6)
  (G.majorantNN Maj.e6ScaleNonnegative 6)
  (λ n → G.majorantStep Maj.e6ScaleNonnegative 6 n ≤-refl)
  (E.e6RealTermBound CM.q G.unit G.envelope)

r : ℝ
r = CM.radius

r2L r2U r3L r3U : Q.ℚᵘ
r2L = rL Q.* rL
r2U = rU Q.* rU
r3L = r2L Q.* rL
r3U = r2U Q.* rU

r2Band : Band r2L (r * r) r2U
r2Band = Rad.squareBand rL rU r (from-yes (Q.0ℚᵘ QP.≤? rL)) Rad.radiusBand

r3Band : Band r3L ((r * r) * r) r3U
r3Band = positiveMul (from-yes (Q.0ℚᵘ QP.≤? r2L)) (from-yes (Q.0ℚᵘ QP.≤? rL))
  r2Band Rad.radiusBand

second4 : G.t4 1 ≃ ((+ 2160 / 1) ⋆) * (r * r)
second4 = let open P.ℝ-Solver in solve 1 (λ r →
  Κ (+ 2160 / 1) ⊗ (((⊝ r) ⊗ (Κ Q.1ℚᵘ ⊗ (⊝ r) ⊖ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ)) ⊖
  Κ Q.0ℚᵘ ⊗ (Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.0ℚᵘ ⊗ (⊝ r))) ⊜ Κ (+ 2160 / 1) ⊗ (r ⊗ r))
  P.≃-refl r

second6 : G.t6 1 ≃ ((+ 16632 / 1) ⋆) * (r * r)
second6 = let open P.ℝ-Solver in solve 1 (λ r →
  Κ (+ 16632 / 1) ⊗ (((⊝ r) ⊗ (Κ Q.1ℚᵘ ⊗ (⊝ r) ⊖ Κ Q.0ℚᵘ ⊗ Κ Q.0ℚᵘ)) ⊖
  Κ Q.0ℚᵘ ⊗ (Κ Q.1ℚᵘ ⊗ Κ Q.0ℚᵘ ⊕ Κ Q.0ℚᵘ ⊗ (⊝ r))) ⊜ Κ (+ 16632 / 1) ⊗ (r ⊗ r))
  P.≃-refl r

x0 y0 : ℝ
x0 = R.1ℝ - ((+ 240 / 1) ⋆) * r + ((+ 2160 / 1) ⋆) * (r * r)
y0 = R.1ℝ + ((+ 504 / 1) ⋆) * r - ((+ 16632 / 1) ⋆) * (r * r)

fourRead : R.1ℝ + Four.ps 2 ≃ x0
fourRead = P.≃-trans (P.+-cong P.≃-refl
  (P.+-cong (P.≃-trans (P.+-identityˡ (G.t4 zero)) G.first4) second4))
  (let open P.ℝ-Solver in solve 1 (λ r →
    Κ Q.1ℚᵘ ⊕ ((⊝ (Κ (+ 240 / 1) ⊗ r)) ⊕ Κ (+ 2160 / 1) ⊗ (r ⊗ r))
      ⊜ Κ Q.1ℚᵘ ⊖ Κ (+ 240 / 1) ⊗ r ⊕ Κ (+ 2160 / 1) ⊗ (r ⊗ r)) P.≃-refl r)

sixRead : R.1ℝ - Six.ps 2 ≃ y0
sixRead = P.≃-trans (P.+-cong P.≃-refl (P.-‿cong
  (P.+-cong (P.≃-trans (P.+-identityˡ (G.t6 zero)) G.first6) second6)))
  (let open P.ℝ-Solver in solve 1 (λ r →
    Κ Q.1ℚᵘ ⊖ ((⊝ (Κ (+ 504 / 1) ⊗ r)) ⊕ Κ (+ 16632 / 1) ⊗ (r ⊗ r))
      ⊜ Κ Q.1ℚᵘ ⊕ Κ (+ 504 / 1) ⊗ r ⊖ Κ (+ 16632 / 1) ⊗ (r ⊗ r)) P.≃-refl r)

eps : Q.ℚᵘ
eps = + 1 / 1000000000000000000000000000000000000000000000

-- Rationally discharge the tiny omitted tail (the 3^6 bound is
-- deliberately retained for E6; no observed cancellation assumed).
budget4 : Four.budget zero ≤ (eps ⋆)
budget4 =
  P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 1 (λ r →
      Κ (+ 16 / 15) ⊗ (Κ (+ 240 / 1) ⊗ (Κ (+ 81 / 1) ⊗ (Κ Q.1ℚᵘ ⊗ r ⊗ r ⊗ r)))
      ⊜ Κ (+ 20736 / 1) ⊗ (r ⊗ r ⊗ r)) P.≃-refl r)
    (proj₂ (widen (from-yes (Q.0ℚᵘ QP.≤? ((+ 20736 / 1) Q.* r3L)))
      (from-yes (((+ 20736 / 1) Q.* r3U) QP.≤? eps))
      (positiveMul (QP.nonNegative⁻¹ (+ 20736 / 1)) (from-yes (Q.0ℚᵘ QP.≤? r3L))
        (constant (+ 20736 / 1)) r3Band)))

budget6 : Six.budget zero ≤ (eps ⋆)
budget6 =
  P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 1 (λ r →
      Κ (+ 16 / 15) ⊗ (Κ (+ 504 / 1) ⊗ (Κ (+ 729 / 1) ⊗ (Κ Q.1ℚᵘ ⊗ r ⊗ r ⊗ r)))
      ⊜ Κ (+ 1959552 / 5) ⊗ (r ⊗ r ⊗ r)) P.≃-refl r)
    (proj₂ (widen (from-yes (Q.0ℚᵘ QP.≤? ((+ 1959552 / 5) Q.* r3L)))
      (from-yes (((+ 1959552 / 5) Q.* r3U) QP.≤? eps))
      (positiveMul (QP.nonNegative⁻¹ (+ 1959552 / 5)) (from-yes (Q.0ℚᵘ QP.≤? r3L))
        (constant (+ 1959552 / 5)) r3Band)))

-- Shift the actual limit bounds; the signs of the E6 unsigned tail
-- are reversed exactly once at the original normalized E6.
xError : (x0 - (eps ⋆) ≤ G.X) × (G.X ≤ x0 + (eps ⋆))
xError =
  let h = Four.limits G.tail4 (C.realConverges (Disk.e4Converges G.Actual.completion))
      open P.ℝ-Solver
  in P.≤-trans (P.+-monoʳ-≤ x0 (P.neg-mono-≤ budget4))
    (P.≤-respˡ-≃
      (P.≃-trans (solve 3 (λ p b z → Κ Q.1ℚᵘ ⊕ (p ⊖ b) ⊜ (Κ Q.1ℚᵘ ⊕ p) ⊖ b)
        P.≃-refl (Four.ps 2) (Four.budget zero) x0) (P.+-cong fourRead P.≃-refl))
      (P.+-monoʳ-≤ R.1ℝ (proj₁ h))) ,
     P.≤-trans (P.≤-respʳ-≃
       (P.≃-trans (P.≃-symm (P.+-assoc R.1ℝ (Four.ps 2) (Four.budget zero)))
         (P.+-cong fourRead P.≃-refl))
       (P.+-monoʳ-≤ R.1ℝ (proj₂ h))) (P.+-monoʳ-≤ x0 budget4)

yError : (y0 - (eps ⋆) ≤ G.Y) × (G.Y ≤ y0 + (eps ⋆))
yError =
  let h = Six.limits G.tail6 (C.realConverges (Disk.e6Converges G.Actual.completion))
      open P.ℝ-Solver
  in P.≤-trans (P.+-monoʳ-≤ y0 (P.neg-mono-≤ budget6))
    (P.≤-respˡ-≃
      (P.≃-trans (solve 2 (λ p b → Κ Q.1ℚᵘ ⊖ (p ⊕ b) ⊜ (Κ Q.1ℚᵘ ⊖ p) ⊖ b)
        P.≃-refl (Six.ps 2) (Six.budget zero)) (P.+-cong sixRead P.≃-refl))
      (P.+-monoʳ-≤ R.1ℝ (P.neg-mono-≤ (proj₂ h)))) ,
     P.≤-trans (P.≤-respʳ-≃
       (P.≃-trans (solve 2 (λ p b → Κ Q.1ℚᵘ ⊖ (p ⊖ b) ⊜ (Κ Q.1ℚᵘ ⊖ p) ⊕ b)
         P.≃-refl (Six.ps 2) (Six.budget zero)) (P.+-cong sixRead P.≃-refl))
       (P.+-monoʳ-≤ R.1ℝ (P.neg-mono-≤ (proj₁ h)))) (P.+-monoʳ-≤ y0 budget6)

x0L x0U y0L y0U : Q.ℚᵘ
x0L = Q.1ℚᵘ Q.- ((+ 240 / 1) Q.* rU) Q.+ ((+ 2160 / 1) Q.* r2L)
x0U = Q.1ℚᵘ Q.- ((+ 240 / 1) Q.* rL) Q.+ ((+ 2160 / 1) Q.* r2U)
y0L = Q.1ℚᵘ Q.+ ((+ 504 / 1) Q.* rL) Q.- ((+ 16632 / 1) Q.* r2U)
y0U = Q.1ℚᵘ Q.+ ((+ 504 / 1) Q.* rU) Q.- ((+ 16632 / 1) Q.* r2L)

x0Band : Band x0L x0 x0U
x0Band = addBand (subBand (constant Q.1ℚᵘ)
  (positiveMul (QP.nonNegative⁻¹ (+ 240 / 1)) (from-yes (Q.0ℚᵘ QP.≤? rL))
    (constant (+ 240 / 1)) Rad.radiusBand))
  (positiveMul (QP.nonNegative⁻¹ (+ 2160 / 1)) (from-yes (Q.0ℚᵘ QP.≤? r2L))
    (constant (+ 2160 / 1)) r2Band)

y0Band : Band y0L y0 y0U
y0Band = subBand (addBand (constant Q.1ℚᵘ)
  (positiveMul (QP.nonNegative⁻¹ (+ 504 / 1)) (from-yes (Q.0ℚᵘ QP.≤? rL))
    (constant (+ 504 / 1)) Rad.radiusBand))
  (positiveMul (QP.nonNegative⁻¹ (+ 16632 / 1)) (from-yes (Q.0ℚᵘ QP.≤? r2L))
    (constant (+ 16632 / 1)) r2Band)

xL xU yL yU : Q.ℚᵘ
xL = x0L Q.- eps
xU = x0U Q.+ eps
yL = y0L Q.- eps
yU = y0U Q.+ eps

enlarge : ∀ {l u : Q.ℚᵘ} {x y : ℝ} →
  Band l x u → (x - (eps ⋆) ≤ y) × (y ≤ x + (eps ⋆)) →
  Band (l Q.- eps) y (u Q.+ eps)
enlarge {l} {u} {x} (hl , hu) (a , b) =
  P.≤-trans (P.≤-respˡ-≃ (P.≃-symm (P.⋆-distrib-to-p⋆-q⋆ l eps))
    (P.+-monoˡ-≤ (R.- (eps ⋆)) hl)) a ,
  P.≤-trans b (P.≤-respʳ-≃ (P.≃-symm (P.⋆-distrib-+ u eps))
    (P.+-monoˡ-≤ (eps ⋆) hu))

xBand : Band xL G.X xU
xBand = enlarge x0Band xError
yBand : Band yL G.Y yU
yBand = enlarge y0Band yError

uL uU vL vU dL dU numL numU : Q.ℚᵘ
uL = (xL Q.* xL) Q.* xL
uU = (xU Q.* xU) Q.* xU
vL = yL Q.* yL
vU = yU Q.* yU
dL = vL Q.- uU
dU = vU Q.- uL
numL = (+ 1728 / 1) Q.* uL
numU = (+ 1728 / 1) Q.* uU

uBand : Band uL (N.cube G.X) uU
uBand = positiveMul (from-yes (Q.0ℚᵘ QP.≤? (xL Q.* xL))) (from-yes (Q.0ℚᵘ QP.≤? xL))
  (Rad.squareBand xL xU G.X (from-yes (Q.0ℚᵘ QP.≤? xL)) xBand) xBand
vBand : Band vL (N.sq G.Y) vU
vBand = Rad.squareBand yL yU G.Y (from-yes (Q.0ℚᵘ QP.≤? yL)) yBand

d : ℝ
d = N.sq G.Y - N.cube G.X

dBand : Band dL d dU
dBand = subBand vBand uBand

dPositive : R.Positive d
dPositive = P.0<x⇒posx (P.<-≤-trans
  (RG.ratLt Q.0ℚᵘ dL (from-yes (Q.0ℚᵘ QP.<? dL))) (proj₁ dBand))

numBand : Band numL (((+ 1728 / 1) ⋆) * N.cube G.X) numU
numBand = positiveMul (QP.nonNegative⁻¹ (+ 1728 / 1)) (from-yes (Q.0ℚᵘ QP.≤? uL))
  (constant (+ 1728 / 1)) uBand

-- The original j quotient, with the sign of its denominator retained.
cross : (d * R.- G.Root.j) ≃ (((+ 1728 / 1) ⋆) * N.cube G.X)
cross = P.≃-trans
  (let open P.ℝ-Solver in solve 3 (λ x y j →
    (y ⊖ x) ⊗ (⊝ j) ⊜ Κ (+ 1728 / 1) ⊗ (j ⊗ (Κ (+ 1 / 1728) ⊗ (x ⊖ y))))
    P.≃-refl (N.cube G.X) (N.sq G.Y) G.Root.j)
  (P.≃-trans (P.*-congˡ (P.*-congˡ (P.≃-symm CM.Selected.deltaRe))) (P.*-congˡ G.Root.jCross))

cl cu : Q.ℚᵘ
cl = + 525074825281535999 / 2
cu = + 525074825281536001 / 2

negJBand : Band cl (R.- G.Root.j) cu
negJBand =
  let lNN = nn cl (QP.nonNegative⁻¹ cl)
      uNN = nn cu (QP.nonNegative⁻¹ cu)
      lo = P.≤-trans (P.*-monoʳ-≤-nonNeg (proj₂ dBand) lNN)
        (P.≤-trans (P.≤-respˡ-≃ (P.⋆-distrib-* dU cl)
          (rat≤ (dU Q.* cl) numL (from-yes ((dU Q.* cl) QP.≤? numL)))) (proj₁ numBand))
      hi = P.≤-trans (proj₂ numBand)
        (P.≤-trans (P.≤-respʳ-≃ (P.⋆-distrib-* dL cu)
          (rat≤ numU (dL Q.* cu) (from-yes (numU QP.≤? (dL Q.* cu)))))
          (P.*-monoʳ-≤-nonNeg (proj₁ dBand) uNN))
  in cancelOrder d dPositive (P.≤-respʳ-≃ (P.≃-symm cross) lo) ,
     cancelOrder d dPositive (P.≤-respˡ-≃ (P.≃-symm cross) hi)

-- From the two signed bounds to the absolute offset, using square-order
-- reflection, not real trichotomy.
offsetLower : R.- Iso.half ≤ Iso.offset
offsetLower =
  P.≤-respˡ-≃
    (let open P.ℝ-Solver in solve 0
      (⊝ Κ cu ⊖ Κ ((Q.- (+ 262537412640768000 / 1))) ⊜ ⊝ Κ (+ 1 / 2)) P.≃-refl)
    (P.≤-respʳ-≃ (P.+-cong (let open P.ℝ-Solver in solve 1 (λ j → ⊝ (⊝ j) ⊜ j)
      P.≃-refl G.Root.j) P.≃-refl)
      (P.+-monoˡ-≤ (R.- J.K) (P.neg-mono-≤ (proj₂ negJBand))))

offsetUpper : Iso.offset ≤ Iso.half
offsetUpper =
  P.≤-respʳ-≃
    (let open P.ℝ-Solver in solve 0
      (⊝ Κ cl ⊖ Κ ((Q.- (+ 262537412640768000 / 1))) ⊜ Κ (+ 1 / 2)) P.≃-refl)
    (P.≤-respˡ-≃ (P.+-cong (let open P.ℝ-Solver in solve 1 (λ j → ⊝ (⊝ j) ⊜ j)
      P.≃-refl G.Root.j) P.≃-refl)
      (P.+-monoˡ-≤ (R.- J.K) (P.neg-mono-≤ (proj₁ negJBand))))

enclosure : ∣ Iso.offset ∣ ≤ Iso.half
enclosure =
  let x = Iso.offset
      h = Iso.half
      open P.ℝ-Solver
      aNN = P.0≤x⇒nonNegx (P.≤-respˡ-≃ (P.+-inverseʳ h)
        (P.+-monoˡ-≤ h (P.neg-mono-≤ offsetUpper)))
      bNN = P.0≤x⇒nonNegx
        (P.≤-respˡ-≃ (solve 1 (λ h → h ⊕ (⊝ h) ⊜ Κ Q.0ℚᵘ) P.≃-refl h)
          (P.+-monoʳ-≤ h offsetLower))
      gap = P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx*y aNN bNN)
      sqBound = P.≤-respˡ-≃ (P.+-identityʳ (x * x))
        (P.≤-respʳ-≃ (solve 2 (λ h x → x ⊗ x ⊕ ((h ⊖ x) ⊗ (h ⊕ x)) ⊜ h ⊗ h)
          P.≃-refl h x) (P.+-monoʳ-≤ (x * x) gap))
      absSq = P.≃-trans (P.≃-symm (P.∣x*y∣≃∣x∣*∣y∣ x x))
        (P.nonNegx⇒∣x∣≃x (Sq.bishopSquareNonnegative x))
  in Reflect.squareReflectsOnNonnegative (P.nonNeg∣x∣ x) Iso.halfNN
    (P.≤-respˡ-≃ (P.≃-symm absSq) sqBound)
