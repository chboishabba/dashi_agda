module DASHI.Moonshine.CM163BishopHecke41DyadicCircleBoundsExact where

-- SOURCE-WRITTEN / KERNEL PENDING.
-- All leaves of the original signed dyadic tree lie on the SAME
-- q-radius. Averaging is nonexpansive in the component box norm.
-- No use of complex roots as a choice principle or classical compactness.
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Product.Base using (_,_; _×_; proj₁; proj₂)
open import Data.Integer.Base using (+_)
open import Data.Rational.Unnormalised using (_/_; 0ℚᵘ; 1ℚᵘ)
import Real as R
open R using (ℝ; _≃_; _≤_; _+_; _*_; _⋆; ∣_∣)
import RealProperties as P
import DASHI.Analysis.BishopComplexSeriesConvergenceExact as C
import DASHI.Analysis.BishopComplexAlgebraExact as A
import DASHI.Analysis.BishopComplexNormSquarePowerEnvelopeExact as Norm
import DASHI.Foundations.BishopExponentialSetoidCongruenceExact as Exp
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneLatticeDenominatorExact as U
import DASHI.Moonshine.JInvariantBishopUpperHalfPlaneRadiusExact as Radius
import DASHI.Moonshine.JInvariantBishopOriginalDyadicRowTransportExact as Phase
import DASHI.Moonshine.JInvariantBishopUnitDiskEisensteinCompletionExact as Unit
import DASHI.Moonshine.JInvariantBishopHomogeneousKleinTransportExact as Cancel
import DASHI.Moonshine.CM163BishopHecke41DyadicFourierProjectionExact as Fourier
import DASHI.Moonshine.CM163BishopHecke41CuspContractionExact as Contract
import DASHI.Moonshine.CM163BishopHecke41UniformCuspBoundExact as Bound
import DASHI.Moonshine.CM163BishopHecke41PowerDifferenceSeriesExact as D
import DASHI.Moonshine.JInvariantBishopPuncturedLatticeEisensteinCompilerExact as Comp
import DASHI.Physics.YangMills.YangMillsSubmissionBishopCutsetExact as Round11
open C using (BishopComplex; _≈C_)
open Comp using (complexTrans; complexSym)
open Fourier using (Point; Func; left; right; pair; mean)
open Contract using (Box; boxCong)

height : Point → ℝ
height p = C.im (U.tau p)

raise : Point → Point
raise p = U.bishop-upper-half-plane-point
  (A.scaleC Radius.two (U.tau p))
  (Cancel.positiveMul Radius.twoPositive (U.imaginaryPositive p))

root : Nat → Point → Point
root zero p = p
root (suc k) p = raise (root k p)

after : Nat → ℝ → ℝ
after zero y = y
after (suc k) y = after k (Phase.half * y)

afterCong : ∀ k {x y} → x ≃ y → after k x ≃ after k y
afterCong zero h = h
afterCong (suc k) h = afterCong k (P.*-congˡ h)

rootHeight : ∀ k p → after k (height (root k p)) ≃ height p
rootHeight zero p = P.≃-refl
rootHeight (suc k) p = P.≃-trans
  (afterCong k (let open P.ℝ-Solver in solve 1
    (λ y → Κ (+ 1 / 2) ⊗ (Κ (+ 2 / 1) ⊗ y) ⊜ y)
    P.≃-refl (height (root k p))))
  (rootHeight k p)

-- Proof-relevant leaf predicate, without creating 2^k explicit points.
Leaves : Nat → Point → (Point → Set) → Set
Leaves zero p F = F p
Leaves (suc k) p F = Leaves k (left p) F × Leaves k (right p) F

mapLeaves : ∀ k p {F G : Point → Set} →
  (∀ v → F v → G v) → Leaves k p F → Leaves k p G
mapLeaves zero p h leaves = h p leaves
mapLeaves (suc k) p h (l , r) =
  mapLeaves k (left p) h l , mapLeaves k (right p) h r

heightLeaves : ∀ k p y → after k (height p) ≃ y →
  Leaves k p (λ v → height v ≃ y)
heightLeaves zero p y h = h
heightLeaves (suc k) p y h = heightLeaves k (left p) y h ,
  heightLeaves k (right p) y h

circleLeaves : ∀ k p → Leaves k (root k p) (λ v → height v ≃ height p)
circleLeaves k p = heightLeaves k (root k p) (height p) (rootHeight k p)

-- Inner-first and outer-first are the same fold, not an exchange
-- of limits. This allows arbitrary leaf-wise bounds to propagate.
meanOuter : ∀ k f p → mean (suc k) f p ≈C pair (mean k f) p
meanOuter zero f p = C.≈C-refl _
meanOuter (suc k) f p = meanOuter k (pair f) p

halfNN : R.NonNegative Phase.half
halfNN = P.0<x⇒nonNegx Phase.halfPositive

halfBound : ∀ M a b → ∣ a ∣ ≤ M → ∣ b ∣ ≤ M →
  ∣ Phase.half * (a + b) ∣ ≤ M
halfBound M a b ha hb =
  let triangle = P.≤-trans (P.∣x+y∣≤∣x∣+∣y∣ a b) (P.+-mono-≤ ha hb)
      eq = P.≃-trans (P.∣x*y∣≃∣x∣*∣y∣ Phase.half (a + b))
        (P.*-congʳ (P.nonNegx⇒∣x∣≃x halfNN))
      finish = let open P.ℝ-Solver in solve 1
        (λ m → Κ (+ 1 / 2) ⊗ (m ⊕ m) ⊜ m) P.≃-refl M
  in P.≤-respˡ-≃ (P.≃-symm eq)
    (P.≤-respʳ-≃ finish (P.*-monoˡ-≤-nonNeg triangle halfNN))

pairBox : ∀ M f p → Box M (f (left p)) → Box M (f (right p)) →
  Box M (pair f p)
pairBox M f p a b = halfBound M _ _ (proj₁ a) (proj₁ b) ,
  halfBound M _ _ (proj₂ a) (proj₂ b)

meanBox : ∀ k p M f → Leaves k p (λ v → Box M (f v)) → Box M (mean k f p)
meanBox zero p M f leaves = leaves
meanBox (suc k) p M f (l , r) =
  boxCong (complexSym (meanOuter k f p))
    (pairBox M (mean k f) p
      (meanBox k (left p) M f l) (meanBox k (right p) M f r))

module At (inputs : Round11.BishopCutset) where
  module F = Fourier.At inputs
  module Ph = F.Ph
  q = F.q
  nz = F.nz

  radiusCong : ∀ p v → height p ≃ height v →
    Radius.machinQRadius (height p) ≃ Radius.machinQRadius (height v)
  radiusCong p v h = Exp.bishopExpCongruent
    (P.-‿cong (P.*-congˡ h))

  normHeight : ∀ p v → height p ≃ height v → Norm.normSqC (q p) ≃ Norm.normSqC (q v)
  normHeight p v h = P.≃-trans (Unit.normSquareAgreement (Ph.disk p))
    (P.≃-trans (P.*-cong (radiusCong p v h) (radiusCong p v h))
      (P.≃-symm (Unit.normSquareAgreement (Ph.disk v))))

  sameRadiusLeaves : ∀ k p → Leaves k (root k p) (λ v → Norm.normSqC (q v) ≃ Norm.normSqC (q p))
  sameRadiusLeaves k p = mapLeaves k (root k p) (λ v h → normHeight v p h) (circleLeaves k p)

  -- Multiplying by (q_ref/q_leaf)^n has unit-radius component
  -- bounds, independent of n and of the sampling depth.
  weight : Point → Nat → Func
  weight p n v = A.powC (Bound.relative (q p) (q v) (nz v)) n

  weightUnit : ∀ p v n → height v ≃ height p → Box R.1ℝ (weight p n v)
  weightUnit p v n h =
    let upper = Bound.relativeUpper (q p) (q v) (nz v)
          (P.≤-reflexive (P.≃-symm (normHeight v p h)))
    in Bound.realUnit upper n , Bound.imagUnit upper n

  weightedBox : ∀ p v n M f → height v ≃ height p → Box M (f v) →
    Box ((Contract.two * M)) (A._*C_ (weight p n v) (f v))
  weightedBox p v n M f h b =
    let w = weight p n v
        z = f v
        u = weightUnit p v n h
        raw = Bound.productBound (C.re z) (C.im z) (C.re w) (C.im w) M (proj₁ b) (proj₂ b)
        -- Any component box bound gives nonnegativity of M.
        nn = P.0≤x⇒nonNegx (P.≤-trans (P.0≤∣x∣ (C.re z)) (proj₁ b))
        eq = let open P.ℝ-Solver in solve 0
          (Κ 1ℚᵘ ⊕ Κ 1ℚᵘ ⊜ Κ (+ 2 / 1)) P.≃-refl
        le = P.*-monoʳ-≤-nonNeg
          (P.≤-respʳ-≃ eq (P.+-mono-≤ (proj₁ u) (proj₂ u))) nn
    in P.≤-trans (proj₁ raw) le , P.≤-trans (proj₂ raw) le

  weightedAverageBound : ∀ k p n M f → (∀ v → Box M (f v)) →
    Box (Contract.two * M)
      (mean k (λ v → A._*C_ (weight p n v) (f v)) (root k p))
  weightedAverageBound k p n M f hb = meanBox k (root k p) (Contract.two * M) _
    (mapLeaves k (root k p) (λ v h → weightedBox p v n M f h (hb v)) (circleLeaves k p))
