module DASHI.Moonshine.JInvariantBishopRectangleRowLimitAttachmentExact where

-- SOURCE-WRITTEN, kernel pending. The existing rectangular exhaustion
-- and finite row-fold permutation are now connected by an actual finite
-- sum limit; only individual row identities remain inputs.
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Nat.Base using (_⊔_)
import Data.Nat.Properties as NP
open import Data.List.Base using (List; []; _∷_; allFin)
open import Data.Product.Base using (_,_; proj₁; proj₂)
open import Data.Integer.Base using (ℤ)
import Real as R
import RealProperties as P
import Sequence as Seq
import DASHI.Analysis.BishopPowerFirstOrderDifferenceFactorisationExact as Power
import DASHI.Moonshine.JInvariantBishopDyadicReciprocalLimitExact as Inv
import DASHI.Physics.Closure.NSTriadKNExactLatticeShellTriads as Cube
import DASHI.Physics.Closure.TriadicEisensteinTransformationTheorem as L
import DASHI.Moonshine.JInvariantBishopLatticeEisensteinKernelExact as K
import DASHI.Moonshine.JInvariantBishopPuncturedShellFiniteFoldExact as F
import DASHI.Moonshine.JInvariantBishopSquareExhaustionExact as Ex
import DASHI.Moonshine.JInvariantBishopSquareShellReindexExact as Re
import DASHI.Moonshine.JInvariantBishopRectangleExhaustionExact as Rect
import DASHI.Moonshine.JInvariantBishopRectangleRowFoldExact as Fold

-- Finite sums of actual convergent rows, with no uniformity in the
-- horizontal coordinate assumed. The fixed horizontal prefix is finite.
listLimit : ∀ {A : Set} (f : A → Nat → R.ℝ) (v : A → R.ℝ) →
  (∀ x → Seq._ConvergesTo_ (f x) (v x)) → ∀ xs →
  Seq._ConvergesTo_ (λ n → Re.sum (λ x → f x n) xs) (Re.sum v xs)
listLimit f v cv [] = Power.constantConverges R.0ℝ
listLimit f v cv (x ∷ xs) = Inv.addR (cv x) (listLimit f v cv xs)

-- Cofinal vertical schedule m ↦ max(n,m) already present in Rect.
-- The original convergence modulus applies because m ≤ max(n,m).
maxLimit : ∀ n {f : Nat → R.ℝ} {v} → Seq._ConvergesTo_ f v →
  Seq._ConvergesTo_ (λ m → f (n ⊔ m)) v
maxLimit n (Seq.con* cv) = Seq.con* λ { (suc k) →
  proj₁ (cv (suc k)) , λ m past →
    proj₂ (cv (suc k)) (n ⊔ m)
      (NP.<-≤-trans past (NP.m≤n⊔m n m)) }

module At
  (f : K.NonzeroLatticePoint → R.ℝ) (respect : Re.PointRespect f)
  (v a : R.ℝ)
  (shell : Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellComponent k f)) v)
  (absolute : Seq._ConvergesTo_ (Seq.SeriesOf (λ k → F.shellAbsolute k f)) a)
  where
  module X = Rect.At f respect v a shell absolute

  rowPrefix : ℤ → Nat → R.ℝ
  rowPrefix j m = Re.sum
    (λ i → Ex.raw f (L.lattice-point j (Cube.decodeCoordinate m i)))
    (allFin (Cube.coordinateCodeBound m))

  rows : (ℤ → R.ℝ) → Nat → R.ℝ
  rows value n = Re.sum (λ i → value (Cube.decodeCoordinate n i))
    (allFin (Cube.coordinateCodeBound n))

  finiteRowLimit : ∀ value →
    (∀ j → Seq._ConvergesTo_ (rowPrefix j) (value j)) →
    ∀ n → Seq._ConvergesTo_ (X.rect n) (rows value n)
  finiteRowLimit value cv n =
    Seq.xₙ≃yₙ∧xₙ→x₀⇒yₙ→x₀
      (λ {(suc m) → P.≃-symm (Fold.finiteRows (Ex.raw f) n (suc m))})
      (rows value n ,
        listLimit (λ i m → rowPrefix (Cube.decodeCoordinate n i) (n ⊔ m))
          (λ i → value (Cube.decodeCoordinate n i))
          (λ i → maxLimit n (cv (Cube.decodeCoordinate n i)))
          (allFin (Cube.coordinateCodeBound n)))

  -- The desired limit of the actual finite row sums is constructed,
  -- not taken as an interchange hypothesis.
  actualRowSum : ∀ value →
    (∀ j → Seq._ConvergesTo_ (rowPrefix j) (value j)) →
    Seq._ConvergesTo_ (rows value) v
  actualRowSum value cv = X.iterated (rows value) (finiteRowLimit value cv)
