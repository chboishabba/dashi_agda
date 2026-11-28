module DASHI.Moonshine.CM163BishopHecke41LocatedOrbitReductionExact where

-- SOURCE-WRITTEN / KERNEL PENDING. Finite fuel, not an appeal to
-- termination of a real-valued Euclidean algorithm. Overlapping
-- located thresholds avoid equality decisions on Bishop reals.
open import Agda.Builtin.Nat using (Nat; zero; suc; _*_)
open import Data.Integer.Base using (+_; -[1+_])
open import Data.Rational.Unnormalised using (ℚᵘ; _/_; 0ℚᵘ; 1ℚᵘ)
import Data.Rational.Unnormalised.Properties as QP
open import Relation.Nullary.Decidable.Core using (from-yes)
open import Data.Sum.Base using (inj₁; inj₂)
open import Data.Product.Base using (_,_; proj₁; proj₂)
import Real as R
open R using (ℝ; _≃_; _≤_; _<_; _+_; _-_; _*_; _⋆; ∣_∣)
import RealProperties as P
import Inverse as I
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexReciprocalExact as Rec
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopExponentialSeriesConvergenceExact as Exp
import DASHI.Foundations.BishopCubicTranslationIteratedExact as NR
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopLatticeGeneratorSummandExact as Gen
import DASHI.Moonshine.CM163BishopHecke41ActualReciprocalRayTransportExact as Ray
import DASHI.Moonshine.CM163BishopHecke41QuantitativeRigidityExact as Rig
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
open Rig using (Orbit; stay; stepS; stepT; backS; backT; same)
open C using (_≈C_)

Point = U.BishopUpperHalfPlanePoint
x y : Point → ℝ
x p = C.re (U.tau p)
y p = C.im (U.tau p)

third half twoThird fourThird threeQuarter : ℝ
third = (+ 1 / 3) ⋆
half = (+ 1 / 2) ⋆
twoThird = (+ 2 / 3) ⋆
fourThird = (+ 4 / 3) ⋆
threeQuarter = (+ 3 / 4) ⋆

thirdPos : R.0ℝ < third
thirdPos = P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 1 / 3) (from-yes (0ℚᵘ QP.<? (+ 1 / 3)))
thirdHalf : third < half
thirdHalf = P.p<q⇒p⋆<q⋆ (+ 1 / 3) (+ 1 / 2) (from-yes ((+ 1 / 3) QP.<? (+ 1 / 2)))
thirdTwoThird : third < twoThird
thirdTwoThird = P.p<q⇒p⋆<q⋆ (+ 1 / 3) (+ 2 / 3) (from-yes ((+ 1 / 3) QP.<? (+ 2 / 3)))
thirdOne : third ≤ R.1ℝ
thirdOne = P.p≤q⇒p⋆≤q⋆ (+ 1 / 3) 1ℚᵘ (from-yes ((+ 1 / 3) QP.≤? 1ℚᵘ))
twoThirdNN : R.NonNegative twoThird
twoThirdNN = P.0≤x⇒nonNegx (P.<⇒≤ (P.<-trans thirdPos thirdTwoThird))

join : ∀ {p v w} → Orbit p v → Orbit v w → Orbit p w
join a (stay _) = a
join a (stepS b) = stepS (join a b)
join a (stepT b) = stepT (join a b)
join a (backS b) = backS (join a b)
join a (backT b) = backT (join a b)
join a (same b e) = same (join a b) e

minusEdge : ∀ p → Orbit p (Ray.minusT p)
minusEdge p = backT (same (stay p) (Comp.complexSym (Ray.undoT p)))

-- An explicit left and right bracket; no decidability of |x|.
record Centered (p : Point) : Set where
  field
    point : Point
    word : Orbit p point
    height : y point ≃ y p
    lower : R.- twoThird ≤ x point
    upper : x point ≤ twoThird

plusN : Nat → Point → Point
plusN zero p = p
plusN (suc n) p = Gen.actT (plusN n p)

plusWord : ∀ n p → Orbit p (plusN n p)
plusWord zero p = stay p
plusWord (suc n) p = stepT (plusWord n p)

plusY : ∀ n p → y (plusN n p) ≃ y p
plusY zero p = P.≃-refl
plusY (suc n) p = plusY n p

plusX : ∀ n p → x (plusN n p) ≃ (x p + NR.natReal n)
plusX zero p = P.≃-symm (P.+-identityʳ (x p))
plusX (suc n) p = P.≃-trans (P.+-cong (plusX n p) P.≃-refl)
  (P.≃-trans (P.+-assoc (x p) (NR.natReal n) R.1ℝ)
    (P.+-cong P.≃-refl (P.≃-symm (NR.natRealSuccessor n))))

negAbsBelow : ∀ a → R.- ∣ a ∣ ≤ a
negAbsBelow a = P.≤-respˡ-≃ (P.-‿cong P.∣-x∣≃∣x∣)
  (P.≤-respʳ-≃ (P.neg-involutive a) (P.neg-mono-≤ (P.x≤∣x∣ {x = R.- a})))

-- Start with a nonnegative translate and walk left until centered.
-- At each left step the upper budget loses exactly one unit.
leftFuel : ∀ n p → R.- twoThird ≤ x p →
  x p ≤ (NR.natReal n + twoThird) → Centered p
leftFuel zero p lo hi = record
  { point = p ; word = stay p ; height = P.≃-refl ; lower = lo
  ; upper = P.≤-respʳ-≃ (P.+-identityˡ twoThird) hi }
leftFuel (suc n) p lo hi with P.fast-corollary-2-17 (x p) third twoThird thirdTwoThird
... | inj₁ h = record
  { point = p ; word = stay p ; height = P.≃-refl ; lower = lo ; upper = P.<⇒≤ h }
... | inj₂ h =
  let v = Ray.minusT p
      -- commute the translation explicitly on each side
      low' : R.- twoThird ≤ x v
      low' = P.≤-respʳ-≃ (P.+-comm (R.- R.1ℝ) (x p))
        (P.≤-respˡ-≃
          (let open P.ℝ-Solver in solve 0
            ((⊝ Κ 1ℚᵘ) ⊕ Κ (+ 1 / 3) ⊜ ⊝ Κ (+ 2 / 3))) P.≃-refl)
          (P.+-monoʳ-≤ (R.- R.1ℝ) (P.<⇒≤ h)))
      up : x v ≤ (NR.natReal n + twoThird)
      up = P.≤-respˡ-≃ (P.+-comm (R.- R.1ℝ) (x p))
        (P.≤-respʳ-≃
          (P.≃-trans (P.+-cong P.≃-refl (P.+-cong (NR.natRealSuccessor n) P.≃-refl))
            (let open P.ℝ-Solver in solve 1
              (λ n → (⊝ Κ 1ℚᵘ) ⊕ ((n ⊕ Κ 1ℚᵘ) ⊕ Κ (+ 2 / 3)) ⊜ n ⊕ Κ (+ 2 / 3))
              P.≃-refl (NR.natReal n)))
          (P.+-monoʳ-≤ (R.- R.1ℝ) hi))
      c = leftFuel n v low' up
  in record { point = Centered.point c ; word = join (minusEdge p) (Centered.word c)
            ; height = Centered.height c ; lower = Centered.lower c ; upper = Centered.upper c }

center : ∀ p → Centered p
center p =
  let n = Exp.magnitudeNaturalBound (x p)
      N = NR.natReal n
      h = P.<⇒≤ (Exp.magnitudeBelowNaturalBound (x p))
      lo = P.≤-trans (P.neg-mono-≤ h) (negAbsBelow (x p))
      hi = P.≤-trans (P.x≤∣x∣ {x = x p}) h
      v = plusN n p
      v0 : R.0ℝ ≤ x v
      v0 = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
             (λ N → N ⊕ (⊝ N) ⊜ Κ 0ℚᵘ) P.≃-refl N)
           (P.≤-respʳ-≃ (P.≃-trans (P.+-comm N (x p)) (P.≃-symm (plusX n p)))
             (P.+-monoʳ-≤ N lo))
      vHi : x v ≤ (NR.natReal (2 * n) + twoThird)
      vHi = P.≤-respˡ-≃ (P.≃-symm (plusX n p))
        (P.≤-trans (P.+-mono-≤ hi P.≤-refl)
          (P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
              (λ N → Κ (+ 2 / 1) ⊗ N ⊜ N ⊕ N) P.≃-refl N)
            (P.≤-respʳ-≃ (P.+-cong (P.≃-symm (NR.natRealMul 2 n)) P.≃-refl)
              (P.≤-respˡ-≃ (P.+-identityʳ ((+ 2 / 1) ⋆ * N))
                (P.+-monoʳ-≤ ((+ 2 / 1) ⋆ * N) (P.nonNegx⇒0≤x twoThirdNN))))))
      low = P.≤-trans (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 0
             (⊝ Κ 0ℚᵘ ⊜ Κ 0ℚᵘ) P.≃-refl) (P.neg-mono-≤ (P.nonNegx⇒0≤x twoThirdNN))) v0
      c = leftFuel (2 * n) v low vHi
  in record { point = Centered.point c ; word = join (plusWord n p) (Centered.word c)
            ; height = P.≃-trans (Centered.height c) (plusY n p)
            ; lower = Centered.lower c ; upper = Centered.upper c }

-- Square bound via (b-a)(b+a) >= 0, valid without a sign split.
squareBracket : ∀ a b → R.- b ≤ a → a ≤ b → (a * a) ≤ (b * b)
squareBracket a b lo hi =
  let l = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
            (λ b → b ⊕ (⊝ b) ⊜ Κ 0ℚᵘ) P.≃-refl b)
            (P.+-monoʳ-≤ b lo)
      r = P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
            (λ a → (⊝ a) ⊕ a ⊜ Κ 0ℚᵘ) P.≃-refl a)
            (P.+-monoʳ-≤ (R.- a) hi)
      prod = P.nonNegx⇒0≤x (P.nonNegx,y⇒nonNegx*y (P.0≤x⇒nonNegx r) (P.0≤x⇒nonNegx l))
      eq = let open P.ℝ-Solver in solve 2
            (λ a b → ((⊝ a) ⊕ b) ⊗ (b ⊕ a) ⊜ b ⊗ b ⊖ a ⊗ a)
            P.≃-refl a b
      shifted = P.+-monoʳ-≤ (a * a) (P.≤-respʳ-≃ eq prod)
  in P.≤-respˡ-≃ (P.+-identityʳ (a * a))
       (P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 2
         (λ a b → a ⊗ a ⊕ (b ⊗ b ⊖ a ⊗ a) ⊜ b ⊗ b)
         P.≃-refl a b) shifted)

normSmall : ∀ p → R.- twoThird ≤ x p → x p ≤ twoThird →
  y p < half → Norm.normSqC (U.tau p) < threeQuarter
normSmall p lo hi hy =
  let yn = P.0≤x⇒nonNegx (P.<⇒≤ (U.imaginaryPositive p))
      xx = squareBracket (x p) twoThird lo hi
      yy = P.*-mono-≤ yn yn (P.<⇒≤ hy) (P.<⇒≤ hy)
      cap = P.+-mono-≤ xx yy
      rat = P.p<q⇒p⋆<q⋆ (+ 25 / 36) (+ 3 / 4) (from-yes ((+ 25 / 36) QP.<? (+ 3 / 4)))
      eq = let open P.ℝ-Solver in solve 0
        (Κ (+ 2 / 3) ⊗ Κ (+ 2 / 3) ⊕ Κ (+ 1 / 2) ⊗ Κ (+ 1 / 2) ⊜ Κ (+ 25 / 36)) P.≃-refl
  in P.≤-<-trans (P.≤-respʳ-≃ eq cap) rat

-- Multiply d < 3/4 by the actual positive reciprocal; no rounding.
heightGain : ∀ p → R.- twoThird ≤ x p → x p ≤ twoThird →
  y p < half → (fourThird * y p) ≤ y (Gen.actS p)
heightGain p lo hi hy =
  let d = Norm.normSqC (U.tau p)
      nz = Rec.normSquareNonzero (Gen.tauNZ p)
      i = I._⁻¹ d nz
      ip = P.0<x⇒posx (I.0<x⇒0<x⁻¹ nz (Rec.normSquarePositive (Gen.tauNZ p)))
      h = P.*-monoʳ-<-pos ip (normSmall p lo hi hy)
      one = P.≃-trans (P.*-comm i d) (I.*-inverseʳ d nz)
      h' = P.<-respˡ-≃ one h
      fpos = P.0<x⇒posx (P.p<q⇒p⋆<q⋆ 0ℚᵘ (+ 4 / 3) (from-yes (0ℚᵘ QP.<? (+ 4 / 3))))
      scaled = P.*-monoʳ-<-pos fpos h'
      invBound = P.<-respˡ-≃ (P.*-identityʳ fourThird)
        (P.<-respʳ-≃ (let open P.ℝ-Solver in solve 1
          (λ i → Κ (+ 4 / 3) ⊗ (i ⊗ Κ (+ 3 / 4)) ⊜ i) P.≃-refl i) scaled)
      gain = P.*-monoˡ-<-pos (P.0<x⇒posx (U.imaginaryPositive p)) invBound
  in P.<⇒≤ (P.<-respʳ-≃ (let open P.ℝ-Solver in solve 2
       (λ i y → i ⊗ y ⊜ ⊝ (i ⊗ (⊝ y))) P.≃-refl i (y p)) gain)

record High (p : Point) : Set where
  field
    point : Point
    word : Orbit p point
    height : third ≤ y point

-- An additive budget suffices: while y >= initial, every inversion
-- gains at least initial/3. The remaining fuel is spent against
-- y + n*delta >= 1/3, so the zero-fuel branch is already high.
module Lift (initial : Point) where
  delta = third * y initial
  deltaPos : R.0ℝ < delta
  deltaPos = P.posx⇒0<x (P.posx,y⇒posx*y (P.0<x⇒posx thirdPos)
    (P.0<x⇒posx (U.imaginaryPositive initial)))

  climb : ∀ n p → y initial ≤ y p →
    third ≤ (y p + NR.natReal n * delta) → High p
  climb zero p base enough = record
    { point = p ; word = stay p
    ; height = P.≤-respʳ-≃ (let open P.ℝ-Solver in solve 2
      (λ y d → y ⊕ Κ 0ℚᵘ ⊗ d ⊜ y) P.≃-refl (y p) delta) enough }
  climb (suc n) p base enough with P.fast-corollary-2-17 (y p) third half thirdHalf
  ... | inj₂ high = record { point = p ; word = stay p ; height = P.<⇒≤ high }
  ... | inj₁ low =
    let c = center p
        v = Centered.point c
        w = Gen.actS v
        hv = Centered.height c
        yv = P.≤-respʳ-≃ (P.≃-symm hv) base
        gain = heightGain v (Centered.lower c) (Centered.upper c) (P.<-respˡ-≃ (P.≃-symm hv) low)
        dBound = P.*-monoʳ-≤-nonNeg yv (P.0≤x⇒nonNegx (P.<⇒≤ thirdPos))
        addGain = P.≤-trans (P.+-mono-≤ P.≤-refl dBound)
          (P.≤-respˡ-≃ (let open P.ℝ-Solver in solve 1
            (λ y → Κ (+ 4 / 3) ⊗ y ⊜ y ⊕ Κ (+ 1 / 3) ⊗ y) P.≃-refl (y v)) gain)
        now : (y p + delta) ≤ y w
        now = P.≤-respˡ-≃ (P.+-cong hv P.≃-refl) addGain
        yp : y p ≤ y w
        yp = P.≤-trans (P.≤-respˡ-≃ (P.+-identityʳ (y p))
          (P.+-monoʳ-≤ (y p) (P.<⇒≤ deltaPos))) now
        next : third ≤ (y w + NR.natReal n * delta)
        next = P.≤-trans enough
          (P.≤-respˡ-≃
            (P.≃-trans (P.+-comm (y p + delta) (NR.natReal n * delta))
              (P.≃-trans (let open P.ℝ-Solver in solve 3
                (λ n d y → (n ⊗ d) ⊕ (y ⊕ d) ⊜ y ⊕ (n ⊕ Κ 1ℚᵘ) ⊗ d)
                P.≃-refl (NR.natReal n) delta (y p))
                (P.+-cong P.≃-refl (P.*-congʳ (P.≃-symm (NR.natRealSuccessor n))))))
            (P.+-mono-≤ now P.≤-refl))
        result = climb n w (P.≤-trans base yp) next
    in record { point = High.point result ; height = High.height result
              ; word = join (stepS (Centered.word c)) (High.word result) }

  -- Archimedean fuel is computed from the reciprocal of the SAME
  -- positive increment, not supplied as an orbit existence axiom.
  inv = I._⁻¹ delta (inj₂ deltaPos)
  fuel = Exp.magnitudeNaturalBound inv
  fuelEnough : third ≤ (y initial + NR.natReal fuel * delta)
  fuelEnough =
    let h = P.≤-trans (P.x≤∣x∣ {x = inv}) (P.<⇒≤ (Exp.magnitudeBelowNaturalBound inv))
        mul = P.*-monoˡ-≤-nonNeg h (P.0≤x⇒nonNegx (P.<⇒≤ deltaPos))
        one = P.≤-respˡ-≃ (I.*-inverseˡ delta (inj₂ deltaPos)) mul
        more = P.≤-respˡ-≃ (P.+-identityˡ (NR.natReal fuel * delta))
          (P.+-mono-≤ (P.<⇒≤ (U.imaginaryPositive initial)) P.≤-refl)
    in P.≤-trans thirdOne (P.≤-trans one more)

  result : High initial
  result = climb fuel initial P.≤-refl fuelEnough

reduce : ∀ p → High p
reduce p = Lift.result p
