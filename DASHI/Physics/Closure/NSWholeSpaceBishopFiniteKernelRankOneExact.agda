module DASHI.Physics.Closure.NSWholeSpaceBishopFiniteKernelRankOneExact where

------------------------------------------------------------------------
-- A / BISHOP-REAL FINITE KERNEL RANK-ONE COMPILER
--
-- Setoid-real port of the generic finite algebra used by periodic R444.
--
-- If pointwise
--
--   K(i,j) ~= beta u(i)u(j) + R(i,j),
--
-- then on every finite list
--
--   Q_K(z) ~= beta (sum_i u(i)z(i))^2 + Q_R(z).
--
-- Likewise
--
--   Q_{d K d}(z) ~= Q_K(d z).
--
-- This is finite Bishop-real ring algebra only.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Unnormalised using (_/_; +_; Κ)

import Real as BishopReal
import RealProperties as BishopP

two : BishopReal.ℝ
two = BishopReal._+_ BishopReal.1ℝ BishopReal.1ℝ

rowSum :
  ∀ {A : Set} →
  (A → A → BishopReal.ℝ) →
  (A → BishopReal.ℝ) →
  A → List A → BishopReal.ℝ
rowSum K z head [] = BishopReal.0ℝ
rowSum K z head (cell ∷ rest) =
  BishopReal._+_
    (BishopReal._*_ (K head cell) (z cell))
    (rowSum K z head rest)

quadraticForm :
  ∀ {A : Set} →
  (A → A → BishopReal.ℝ) →
  (A → BishopReal.ℝ) →
  List A → BishopReal.ℝ
quadraticForm K z [] = BishopReal.0ℝ
quadraticForm K z (head ∷ rest) =
  BishopReal._+_
    (BishopReal._+_
      (BishopReal._*_
        (BishopReal._*_ (K head head) (z head))
        (z head))
      (BishopReal._*_
        two
        (BishopReal._*_
          (z head)
          (rowSum K z head rest))))
    (quadraticForm K z rest)

linearSum :
  ∀ {A : Set} →
  (A → BishopReal.ℝ) →
  (A → BishopReal.ℝ) →
  List A → BishopReal.ℝ
linearSum u z [] = BishopReal.0ℝ
linearSum u z (cell ∷ rest) =
  BishopReal._+_
    (BishopReal._*_ (u cell) (z cell))
    (linearSum u z rest)

rowRankOneSplit :
  ∀ {A : Set}
    (K R : A → A → BishopReal.ℝ)
    (u z : A → BishopReal.ℝ)
    (beta : BishopReal.ℝ)
    (pointwise : (left right : A) →
      BishopReal._≃_
        (K left right)
        (BishopReal._+_
          (BishopReal._*_
            beta
            (BishopReal._*_
              (u left) (u right)))
          (R left right)))
    (head : A) (items : List A) →
  BishopReal._≃_
    (rowSum K z head items)
    (BishopReal._+_
      (BishopReal._*_
        beta
        (BishopReal._*_
          (u head)
          (linearSum u z items)))
      (rowSum R z head items))
rowRankOneSplit K R u z beta pointwise head [] =
  let open BishopP.ℝ-Solver
  in solve 2
    (λ b uh →
      Κ (+ 0 / 1)
      ⊜
      (b ⊗ (uh ⊗ Κ (+ 0 / 1)))
        ⊕ Κ (+ 0 / 1))
    BishopP.≃-refl beta (u head)
rowRankOneSplit K R u z beta pointwise head (cell ∷ rest) =
  let
    tail =
      rowRankOneSplit
        K R u z beta pointwise head rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.*-congˡ (pointwise head cell))
      tail)
    (solve 7
      (λ b uh uc zc su sr r →
        (((b ⊗ (uh ⊗ uc)) ⊕ r) ⊗ zc)
          ⊕
          ((b ⊗ (uh ⊗ su)) ⊕ sr)
        ⊜
        (b ⊗
          (uh ⊗ ((uc ⊗ zc) ⊕ su)))
          ⊕ ((r ⊗ zc) ⊕ sr))
      BishopP.≃-refl
      beta (u head) (u cell) (z cell)
      (linearSum u z rest)
      (rowSum R z head rest)
      (R head cell))

quadraticRankOneSplit :
  ∀ {A : Set}
    (K R : A → A → BishopReal.ℝ)
    (u z : A → BishopReal.ℝ)
    (beta : BishopReal.ℝ)
    (pointwise : (left right : A) →
      BishopReal._≃_
        (K left right)
        (BishopReal._+_
          (BishopReal._*_
            beta
            (BishopReal._*_
              (u left) (u right)))
          (R left right)))
    (items : List A) →
  BishopReal._≃_
    (quadraticForm K z items)
    (BishopReal._+_
      (BishopReal._*_
        beta
        (BishopReal._*_
          (linearSum u z items)
          (linearSum u z items)))
      (quadraticForm R z items))
quadraticRankOneSplit K R u z beta pointwise [] =
  let open BishopP.ℝ-Solver
  in solve 1
    (λ b →
      Κ (+ 0 / 1)
      ⊜
      (b ⊗ (Κ (+ 0 / 1) ⊗ Κ (+ 0 / 1)))
        ⊕ Κ (+ 0 / 1))
    BishopP.≃-refl beta
quadraticRankOneSplit K R u z beta pointwise (head ∷ rest) =
  let
    headSplit = pointwise head head
    rowSplit =
      rowRankOneSplit
        K R u z beta pointwise head rest
    tailSplit =
      quadraticRankOneSplit
        K R u z beta pointwise rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.+-cong
        (BishopP.*-cong
          (BishopP.*-cong
            headSplit BishopP.≃-refl)
          BishopP.≃-refl)
        (BishopP.*-cong
          BishopP.≃-refl
          (BishopP.*-cong
            BishopP.≃-refl rowSplit)))
      tailSplit)
    (solve 7
      (λ b uh zh su rh rr qr →
        ((((b ⊗ (uh ⊗ uh)) ⊕ rh)
            ⊗ zh) ⊗ zh)
          ⊕
          ((Κ (+ 2 / 1) ⊗ zh)
            ⊗ ((b ⊗ (uh ⊗ su)) ⊕ rr))
          ⊕
          ((b ⊗ (su ⊗ su)) ⊕ qr)
        ⊜
        (b ⊗
          (((uh ⊗ zh) ⊕ su)
            ⊗ ((uh ⊗ zh) ⊕ su)))
          ⊕
          ((rh ⊗ (zh ⊗ zh))
            ⊕ ((Κ (+ 2 / 1) ⊗ zh) ⊗ rr)
            ⊕ qr))
      BishopP.≃-refl
      beta (u head) (z head)
      (linearSum u z rest)
      (R head head)
      (rowSum R z head rest)
      (quadraticForm R z rest))

scaledKernel :
  ∀ {A : Set} →
  (A → A → BishopReal.ℝ) →
  (A → BishopReal.ℝ) →
  A → A → BishopReal.ℝ
scaledKernel K d left right =
  BishopReal._*_
    (d left)
    (BishopReal._*_
      (K left right)
      (d right))

scaledCoefficient :
  ∀ {A : Set} →
  (A → BishopReal.ℝ) →
  (A → BishopReal.ℝ) →
  A → BishopReal.ℝ
scaledCoefficient d z cell =
  BishopReal._*_ (d cell) (z cell)

rowDiagonalScaling :
  ∀ {A : Set}
    (K : A → A → BishopReal.ℝ)
    (d z : A → BishopReal.ℝ)
    (head : A) (items : List A) →
  BishopReal._≃_
    (rowSum (scaledKernel K d) z head items)
    (BishopReal._*_
      (d head)
      (rowSum K (scaledCoefficient d z) head items))
rowDiagonalScaling K d z head [] =
  BishopP.≃-symm
    (BishopP.*-zeroʳ (d head))
rowDiagonalScaling K d z head (cell ∷ rest) =
  let
    tail = rowDiagonalScaling K d z head rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong BishopP.≃-refl tail)
    (solve 5
      (λ dh dc k zc row →
        (dh ⊗ (k ⊗ dc)) ⊗ zc
          ⊕ (dh ⊗ row)
        ⊜
        dh ⊗ ((k ⊗ (dc ⊗ zc)) ⊕ row))
      BishopP.≃-refl
      (d head) (d cell) (K head cell) (z cell)
      (rowSum K (scaledCoefficient d z) head rest))

quadraticDiagonalScaling :
  ∀ {A : Set}
    (K : A → A → BishopReal.ℝ)
    (d z : A → BishopReal.ℝ)
    (items : List A) →
  BishopReal._≃_
    (quadraticForm (scaledKernel K d) z items)
    (quadraticForm K (scaledCoefficient d z) items)
quadraticDiagonalScaling K d z [] = BishopP.≃-refl
quadraticDiagonalScaling K d z (head ∷ rest) =
  let
    row = rowDiagonalScaling K d z head rest
    tail = quadraticDiagonalScaling K d z rest
    open BishopP.ℝ-Solver
  in
  BishopP.≃-trans
    (BishopP.+-cong
      (BishopP.+-cong
        BishopP.≃-refl
        (BishopP.*-cong
          BishopP.≃-refl
          (BishopP.*-cong
            BishopP.≃-refl row)))
      tail)
    (solve 5
      (λ dh zh khh row' tail' →
        ((dh ⊗ (khh ⊗ dh)) ⊗ (zh ⊗ zh))
          ⊕
          ((Κ (+ 2 / 1) ⊗ zh) ⊗ (dh ⊗ row'))
          ⊕ tail'
        ⊜
        (khh ⊗ ((dh ⊗ zh) ⊗ (dh ⊗ zh)))
          ⊕
          ((Κ (+ 2 / 1) ⊗ (dh ⊗ zh)) ⊗ row')
          ⊕ tail')
      BishopP.≃-refl
      (d head) (z head) (K head head)
      (rowSum K (scaledCoefficient d z) head rest)
      (quadraticForm K (scaledCoefficient d z) rest))

bishopFiniteRankOneQuadraticSplitClosed : Bool
bishopFiniteRankOneQuadraticSplitClosed = true

bishopFiniteDiagonalScalingClosed : Bool
bishopFiniteDiagonalScalingClosed = true

infiniteSeriesUsed : Bool
infiniteSeriesUsed = false

matrixSpectralTheoremUsed : Bool
matrixSpectralTheoremUsed = false

clayPromotion : Bool
clayPromotion = false

bishopFiniteRankOneQuadraticSplitClosedIsTrue :
  bishopFiniteRankOneQuadraticSplitClosed ≡ true
bishopFiniteRankOneQuadraticSplitClosedIsTrue = refl

bishopFiniteDiagonalScalingClosedIsTrue :
  bishopFiniteDiagonalScalingClosed ≡ true
bishopFiniteDiagonalScalingClosedIsTrue = refl

clayPromotionIsFalse : clayPromotion ≡ false
clayPromotionIsFalse = refl
