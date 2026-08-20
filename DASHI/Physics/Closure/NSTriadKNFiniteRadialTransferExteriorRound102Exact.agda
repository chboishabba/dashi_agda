module DASHI.Physics.Closure.NSTriadKNFiniteRadialTransferExteriorRound102Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Fabian Waleffe.
-- Title: "The nature of triad interactions in homogeneous turbulence".
-- Physics of Fluids A 4 (1992), 350--363.
-- DOI: 10.1063/1.858309.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- Springer, 2011.
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND102 / FINITE RADIAL EXTERIOR FACTORIZATION
--
-- This is the arbitrary-finite-radius completion of the Round101 two-radius
-- identity and the Round102 three-radius calculation.
--
-- For radial cells i carrying
--
--   lambda_i, E_i, q_i,
--
-- define
--
--   E = sum E_i,
--   q = sum q_i,
--   D = sum lambda_i E_i,
--   L = sum lambda_i q_i.
--
-- Then the complete recombination defect satisfies the exact finite identity
--
--   D q - E L
--     = sum_{i<j} (lambda_i-lambda_j)(E_i q_j-E_j q_i).
--
-- This is proved by list induction, not recorded as an assumed finite-sum
-- receipt.  The theorem shows that every cross-radius obstruction is carried
-- by the antisymmetric 2x2 minors of the two-column matrix (E_i,q_i), weighted
-- by radial separation.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; -_)
open import Data.Rational.Tactic.RingSolver using (solve)

record RadialTransferCell : Set where
  constructor radial-transfer-cell
  field
    eigenvalue energy transfer : ℚ

open RadialTransferCell public

sub : ℚ → ℚ → ℚ
sub x y = x + (- y)

sumEnergy : List RadialTransferCell → ℚ
sumEnergy [] = 0ℚ
sumEnergy (x ∷ xs) = energy x + sumEnergy xs

sumTransfer : List RadialTransferCell → ℚ
sumTransfer [] = 0ℚ
sumTransfer (x ∷ xs) = transfer x + sumTransfer xs

sumWeightedEnergy : List RadialTransferCell → ℚ
sumWeightedEnergy [] = 0ℚ
sumWeightedEnergy (x ∷ xs) =
  eigenvalue x * energy x + sumWeightedEnergy xs

sumWeightedTransfer : List RadialTransferCell → ℚ
sumWeightedTransfer [] = 0ℚ
sumWeightedTransfer (x ∷ xs) =
  eigenvalue x * transfer x + sumWeightedTransfer xs

radialRecombinationDefect : List RadialTransferCell → ℚ
radialRecombinationDefect xs =
  sub (sumWeightedEnergy xs * sumTransfer xs)
      (sumEnergy xs * sumWeightedTransfer xs)

pairMinor : RadialTransferCell → RadialTransferCell → ℚ
pairMinor x y = sub (energy x * transfer y) (energy y * transfer x)

pairExterior : RadialTransferCell → RadialTransferCell → ℚ
pairExterior x y =
  sub (eigenvalue x) (eigenvalue y) * pairMinor x y

headExteriorSum : RadialTransferCell → List RadialTransferCell → ℚ
headExteriorSum x [] = 0ℚ
headExteriorSum x (y ∷ ys) = pairExterior x y + headExteriorSum x ys

finitePairwiseExteriorSum : List RadialTransferCell → ℚ
finitePairwiseExteriorSum [] = 0ℚ
finitePairwiseExteriorSum (x ∷ xs) =
  headExteriorSum x xs + finitePairwiseExteriorSum xs

headExteriorClosedForm :
  (x : RadialTransferCell) (xs : List RadialTransferCell) →
  headExteriorSum x xs
  ≡
    eigenvalue x * energy x * sumTransfer xs
    + sumWeightedEnergy xs * transfer x
    + (- (energy x * sumWeightedTransfer xs))
    + (- (sumEnergy xs * eigenvalue x * transfer x))
headExteriorClosedForm x [] = solve (eigenvalue x ∷ energy x ∷ transfer x ∷ [])
headExteriorClosedForm x (y ∷ ys)
  rewrite headExteriorClosedForm x ys =
  solve
    ( eigenvalue x ∷ energy x ∷ transfer x
    ∷ eigenvalue y ∷ energy y ∷ transfer y
    ∷ sumEnergy ys ∷ sumTransfer ys
    ∷ sumWeightedEnergy ys ∷ sumWeightedTransfer ys
    ∷ [])

finiteRadialDefectIsPairwiseExteriorSum :
  (xs : List RadialTransferCell) →
  radialRecombinationDefect xs ≡ finitePairwiseExteriorSum xs
finiteRadialDefectIsPairwiseExteriorSum [] = solve []
finiteRadialDefectIsPairwiseExteriorSum (x ∷ xs)
  rewrite finiteRadialDefectIsPairwiseExteriorSum xs
        | headExteriorClosedForm x xs =
  solve
    ( eigenvalue x ∷ energy x ∷ transfer x
    ∷ sumEnergy xs ∷ sumTransfer xs
    ∷ sumWeightedEnergy xs ∷ sumWeightedTransfer xs
    ∷ [])

round102FiniteRadialDefectExteriorFactorizationClosed : Bool
round102FiniteRadialDefectExteriorFactorizationClosed = true

round102FiniteRadialDefectExteriorFactorizationClosedIsTrue :
  round102FiniteRadialDefectExteriorFactorizationClosed ≡ true
round102FiniteRadialDefectExteriorFactorizationClosedIsTrue = refl
