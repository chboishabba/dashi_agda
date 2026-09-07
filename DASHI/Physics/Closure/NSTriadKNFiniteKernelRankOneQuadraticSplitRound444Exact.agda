module DASHI.Physics.Closure.NSTriadKNFiniteKernelRankOneQuadraticSplitRound444Exact where

------------------------------------------------------------------------
-- ROUND444 / FINITE KERNEL RANK-ONE SPLIT -> QUADRATIC-FORM SPLIT
--
-- This is the finite bilinear compiler needed by the R443 Cauchy Schur step.
-- For an arbitrary finite carrier, if pointwise
--
--        K(i,j) = beta u(i)u(j) + R(i,j),
--
-- then exactly
--
--   Q_K(z) = beta (sum_i u(i) z(i))^2 + Q_R(z).
--
-- The second compiler records diagonal scaling:
--
--   Q_{d K d}(z) = Q_K(d z).
--
-- No positivity, topology, matrix library, spectral theorem or infinite series
-- is used.  Both proofs are list induction plus rational ring normalization.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _+_; _*_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong₂; trans)

rowSum :
  ∀ {A : Set} →
  (A → A → ℚ) →
  (A → ℚ) →
  A → List A → ℚ
rowSum K z head [] = 0ℚ
rowSum K z head (cell ∷ rest) =
  K head cell * z cell + rowSum K z head rest

quadraticForm :
  ∀ {A : Set} →
  (A → A → ℚ) →
  (A → ℚ) →
  List A → ℚ
quadraticForm K z [] = 0ℚ
quadraticForm K z (head ∷ rest) =
  K head head * z head * z head
  + (1ℚ + 1ℚ) * z head * rowSum K z head rest
  + quadraticForm K z rest

linearSum :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → ℚ) →
  List A → ℚ
linearSum u z [] = 0ℚ
linearSum u z (cell ∷ rest) =
  u cell * z cell + linearSum u z rest

rowRankOneSplit :
  ∀ {A : Set}
    (K R : A → A → ℚ)
    (u z : A → ℚ)
    (beta : ℚ)
    (pointwise : (left right : A) →
      K left right ≡ beta * u left * u right + R left right)
    (head : A) (items : List A) →
  rowSum K z head items
  ≡ beta * u head * linearSum u z items
      + rowSum R z head items
rowRankOneSplit K R u z beta pointwise head [] =
  solve (beta ∷ u head ∷ [])
rowRankOneSplit K R u z beta pointwise head (cell ∷ rest) =
  trans
    (cong₂ _+_
      (cong₂ _*_
        (pointwise head cell)
        refl)
      (rowRankOneSplit K R u z beta pointwise head rest))
    (solve
      ( beta ∷ u head ∷ u cell ∷ z cell
      ∷ linearSum u z rest
      ∷ rowSum R z head rest
      ∷ R head cell ∷ []))

quadraticRankOneSplit :
  ∀ {A : Set}
    (K R : A → A → ℚ)
    (u z : A → ℚ)
    (beta : ℚ)
    (pointwise : (left right : A) →
      K left right ≡ beta * u left * u right + R left right)
    (items : List A) →
  quadraticForm K z items
  ≡ beta * linearSum u z items * linearSum u z items
      + quadraticForm R z items
quadraticRankOneSplit K R u z beta pointwise [] =
  solve (beta ∷ [])
quadraticRankOneSplit K R u z beta pointwise (head ∷ rest) =
  let
    headSplit = pointwise head head
    rowSplit = rowRankOneSplit K R u z beta pointwise head rest
    tailSplit = quadraticRankOneSplit K R u z beta pointwise rest
  in
  trans
    (cong₂ _+_
      (cong₂ _+_
        (cong₂ _*_
          (cong₂ _*_
            headSplit refl)
          refl)
        (cong₂ _*_
          (cong₂ _*_
            refl refl)
          rowSplit))
      tailSplit)
    (solve
      ( beta ∷ u head ∷ z head
      ∷ linearSum u z rest
      ∷ R head head
      ∷ rowSum R z head rest
      ∷ quadraticForm R z rest ∷ []))

scaledKernel :
  ∀ {A : Set} →
  (A → A → ℚ) →
  (A → ℚ) →
  A → A → ℚ
scaledKernel K d left right = d left * K left right * d right

scaledCoefficient :
  ∀ {A : Set} →
  (A → ℚ) →
  (A → ℚ) →
  A → ℚ
scaledCoefficient d z cell = d cell * z cell

rowDiagonalScaling :
  ∀ {A : Set}
    (K : A → A → ℚ)
    (d z : A → ℚ)
    (head : A) (items : List A) →
  rowSum (scaledKernel K d) z head items
  ≡ d head * rowSum K (scaledCoefficient d z) head items
rowDiagonalScaling K d z head [] = solve (d head ∷ [])
rowDiagonalScaling K d z head (cell ∷ rest) =
  trans
    (cong₂ _+_ refl (rowDiagonalScaling K d z head rest))
    (solve
      ( d head ∷ d cell ∷ K head cell ∷ z cell
      ∷ rowSum K (scaledCoefficient d z) head rest ∷ []))

quadraticDiagonalScaling :
  ∀ {A : Set}
    (K : A → A → ℚ)
    (d z : A → ℚ)
    (items : List A) →
  quadraticForm (scaledKernel K d) z items
  ≡ quadraticForm K (scaledCoefficient d z) items
quadraticDiagonalScaling K d z [] = refl
quadraticDiagonalScaling K d z (head ∷ rest) =
  trans
    (cong₂ _+_
      (cong₂ _+_
        refl
        (cong₂ _*_
          (cong₂ _*_ refl refl)
          (rowDiagonalScaling K d z head rest)))
      (quadraticDiagonalScaling K d z rest))
    (solve
      ( d head ∷ z head ∷ K head head
      ∷ rowSum K (scaledCoefficient d z) head rest
      ∷ quadraticForm K (scaledCoefficient d z) rest ∷ []))

round444FiniteRankOneQuadraticSplitClosed : Bool
round444FiniteRankOneQuadraticSplitClosed = true

round444FiniteDiagonalScalingClosed : Bool
round444FiniteDiagonalScalingClosed = true

round444InfiniteSeriesUsed : Bool
round444InfiniteSeriesUsed = false

round444MatrixSpectralTheoremUsed : Bool
round444MatrixSpectralTheoremUsed = false

round444FiniteRankOneQuadraticSplitClosedIsTrue :
  round444FiniteRankOneQuadraticSplitClosed ≡ true
round444FiniteRankOneQuadraticSplitClosedIsTrue = refl

round444FiniteDiagonalScalingClosedIsTrue :
  round444FiniteDiagonalScalingClosed ≡ true
round444FiniteDiagonalScalingClosedIsTrue = refl
