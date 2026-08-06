module DASHI.Physics.Closure.NSTriadKNLuoSobolevTensorProjectionErrorExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphaël Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- PURPOSE
-- Prove the exact algebra and squared estimate used to pass Galerkin
-- convergence through the nonlinear tensor:
--
--   u⊗u - v⊗v = (u-v)⊗u + v⊗(u-v),
--
-- followed by
--
--   |a+b|² <= 2(|a|²+|b|²).
--
-- The finite energy theorem below sums this estimate cell by cell.  Combined
-- with the weighted Fourier-tail theorem, it is the concrete G3/G4 bridge from
-- projection tails to nonlinear interaction errors.
------------------------------------------------------------------------

open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using
  (ℚ; 0ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality
  using (_≡_; cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

tensorDifference :
  ℚ → ℚ → ℚ → ℚ → ℚ
tensorDifference leftA rightA leftB rightB =
  leftA * rightA - leftB * rightB

leftProjectionError :
  ℚ → ℚ → ℚ → ℚ
leftProjectionError leftA leftB rightA =
  (leftA - leftB) * rightA

rightProjectionError :
  ℚ → ℚ → ℚ → ℚ
rightProjectionError leftB rightA rightB =
  leftB * (rightA - rightB)

tensorDifferenceIdentity :
  (leftA rightA leftB rightB : ℚ) →
  tensorDifference leftA rightA leftB rightB
  ≡ leftProjectionError leftA leftB rightA
    + rightProjectionError leftB rightA rightB
tensorDifferenceIdentity leftA rightA leftB rightB =
  solve (leftA ∷ rightA ∷ leftB ∷ rightB ∷ [])

squareSumDecomposition :
  (left right : ℚ) →
  L2.square (left + right)
  ≡
  ( (L2.square left + L2.square left)
    + (L2.square right + L2.square right)
  )
  - L2.square (left - right)
squareSumDecomposition left right =
  solve (left ∷ right ∷ [])

squareSumAtMostTwice :
  (left right : ℚ) →
  L2.square (left + right)
  ≤
  (L2.square left + L2.square left)
  + (L2.square right + L2.square right)
squareSumAtMostTwice left right =
  subst
    (λ lower →
      lower
      ≤
      (L2.square left + L2.square left)
      + (L2.square right + L2.square right))
    (sym (squareSumDecomposition left right))
    (L2.subtractNonnegativeBelow
      ( (L2.square left + L2.square left)
        + (L2.square right + L2.square right))
      (L2.square (left - right))
      (L2.squareNonnegative (left - right)))

tensorDifferenceSquareBound :
  (leftA rightA leftB rightB : ℚ) →
  L2.square (tensorDifference leftA rightA leftB rightB)
  ≤
  ( L2.square (leftProjectionError leftA leftB rightA)
    + L2.square (leftProjectionError leftA leftB rightA)
  )
  +
  ( L2.square (rightProjectionError leftB rightA rightB)
    + L2.square (rightProjectionError leftB rightA rightB)
  )
tensorDifferenceSquareBound leftA rightA leftB rightB =
  subst
    (λ lower →
      lower
      ≤
      ( L2.square (leftProjectionError leftA leftB rightA)
        + L2.square (leftProjectionError leftA leftB rightA)
      )
      +
      ( L2.square (rightProjectionError leftB rightA rightB)
        + L2.square (rightProjectionError leftB rightA rightB)
      ))
    (sym
      (cong L2.square
        (tensorDifferenceIdentity leftA rightA leftB rightB)))
    (squareSumAtMostTwice
      (leftProjectionError leftA leftB rightA)
      (rightProjectionError leftB rightA rightB))

record TensorProjectionCell : Set where
  constructor tensor-projection-cell
  field
    leftA rightA leftB rightB : ℚ

open TensorProjectionCell public

tensorErrorEnergy : List TensorProjectionCell → ℚ
tensorErrorEnergy [] = 0ℚ
tensorErrorEnergy (cell ∷ cells) =
  L2.square
    (tensorDifference
      (leftA cell) (rightA cell)
      (leftB cell) (rightB cell))
  + tensorErrorEnergy cells

leftProjectionEnergy : List TensorProjectionCell → ℚ
leftProjectionEnergy [] = 0ℚ
leftProjectionEnergy (cell ∷ cells) =
  L2.square
    (leftProjectionError
      (leftA cell) (leftB cell) (rightA cell))
  + leftProjectionEnergy cells

rightProjectionEnergy : List TensorProjectionCell → ℚ
rightProjectionEnergy [] = 0ℚ
rightProjectionEnergy (cell ∷ cells) =
  L2.square
    (rightProjectionError
      (leftB cell) (rightA cell) (rightB cell))
  + rightProjectionEnergy cells

finiteTensorProjectionEnergyBound :
  (cells : List TensorProjectionCell) →
  tensorErrorEnergy cells
  ≤
  (leftProjectionEnergy cells + leftProjectionEnergy cells)
  + (rightProjectionEnergy cells + rightProjectionEnergy cells)
finiteTensorProjectionEnergyBound [] = ℚₚ.≤-refl
finiteTensorProjectionEnergyBound (cell ∷ cells) =
  let
    local =
      tensorDifferenceSquareBound
        (leftA cell) (rightA cell)
        (leftB cell) (rightB cell)

    tail = finiteTensorProjectionEnergyBound cells
    summed = ℚₚ.+-mono-≤ local tail

    rearranged :
      ( ( L2.square
            (leftProjectionError
              (leftA cell) (leftB cell) (rightA cell))
          + L2.square
            (leftProjectionError
              (leftA cell) (leftB cell) (rightA cell))
        )
        +
        ( L2.square
            (rightProjectionError
              (leftB cell) (rightA cell) (rightB cell))
          + L2.square
            (rightProjectionError
              (leftB cell) (rightA cell) (rightB cell))
        )
      )
      +
      ( (leftProjectionEnergy cells + leftProjectionEnergy cells)
        + (rightProjectionEnergy cells + rightProjectionEnergy cells)
      )
      ≡
      ( ( L2.square
            (leftProjectionError
              (leftA cell) (leftB cell) (rightA cell))
          + leftProjectionEnergy cells
        )
        +
        ( L2.square
            (leftProjectionError
              (leftA cell) (leftB cell) (rightA cell))
          + leftProjectionEnergy cells
        )
      )
      +
      ( ( L2.square
            (rightProjectionError
              (leftB cell) (rightA cell) (rightB cell))
          + rightProjectionEnergy cells
        )
        +
        ( L2.square
            (rightProjectionError
              (leftB cell) (rightA cell) (rightB cell))
          + rightProjectionEnergy cells
        )
      )
    rearranged =
      solve
        ( L2.square
            (leftProjectionError
              (leftA cell) (leftB cell) (rightA cell))
        ∷ L2.square
            (rightProjectionError
              (leftB cell) (rightA cell) (rightB cell))
        ∷ leftProjectionEnergy cells
        ∷ rightProjectionEnergy cells
        ∷ [])
  in
  subst
    (λ upper →
      L2.square
        (tensorDifference
          (leftA cell) (rightA cell)
          (leftB cell) (rightB cell))
      + tensorErrorEnergy cells
      ≤ upper)
    rearranged
    summed
