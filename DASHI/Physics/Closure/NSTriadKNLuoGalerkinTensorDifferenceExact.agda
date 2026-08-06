module DASHI.Physics.Closure.NSTriadKNLuoGalerkinTensorDifferenceExact where

------------------------------------------------------------------------
-- PROVENANCE
--
-- Author: John G. Heywood.
-- Title: "An Error Estimate Uniform in Time for Spectral Galerkin
-- Approximations of the Navier-Stokes Problem".
-- Pacific Journal of Mathematics 98 (1982), 333--345.
-- DOI: 10.2140/pjm.1982.98.333.
--
-- Classical PDE reference:
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- PURPOSE
-- Construct the product-difference source used by the Galerkin nonlinear
-- error. Componentwise,
--
--   u_i u_j - v_i v_j
--     = (u_i-v_i) u_j + v_i (u_j-v_j).
--
-- Squaring and summing gives a radical-free finite estimate with factor two.
-- This removes a free tensor-difference producer from the nonlinear
-- approximation lane.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _-_; _≤_)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2
import DASHI.Physics.Closure.NSTriadKNLuoGalerkinInteractionDifferenceExact as Error

productDifferenceIdentity :
  (physicalLeft physicalRight
   approximationLeft approximationRight : ℚ) →
  physicalLeft * physicalRight
    - approximationLeft * approximationRight
  ≡ (physicalLeft - approximationLeft) * physicalRight
    + approximationLeft * (physicalRight - approximationRight)
productDifferenceIdentity
  physicalLeft physicalRight
  approximationLeft approximationRight =
  solve
    ( physicalLeft ∷ physicalRight
    ∷ approximationLeft ∷ approximationRight ∷ [])

record TensorDifferenceCell : Set where
  constructor tensor-difference-cell
  field
    physicalLeft physicalRight : ℚ
    approximationLeft approximationRight : ℚ

open TensorDifferenceCell public

directDifference firstBranch secondBranch : TensorDifferenceCell → ℚ
directDifference cell =
  physicalLeft cell * physicalRight cell
  - approximationLeft cell * approximationRight cell
firstBranch cell =
  (physicalLeft cell - approximationLeft cell) * physicalRight cell
secondBranch cell =
  approximationLeft cell * (physicalRight cell - approximationRight cell)

cellDifferenceMeaning :
  (cell : TensorDifferenceCell) →
  directDifference cell ≡ firstBranch cell + secondBranch cell
cellDifferenceMeaning cell =
  productDifferenceIdentity
    (physicalLeft cell)
    (physicalRight cell)
    (approximationLeft cell)
    (approximationRight cell)

cellDifferenceSquareBound :
  (cell : TensorDifferenceCell) →
  L2.square (directDifference cell)
  ≤ Error.two
    * (L2.square (firstBranch cell) + L2.square (secondBranch cell))
cellDifferenceSquareBound cell =
  subst
    (λ lower →
      lower
      ≤ Error.two
        * (L2.square (firstBranch cell) + L2.square (secondBranch cell)))
    (sym (cong L2.square (cellDifferenceMeaning cell)))
    (Error.squareSumBound (firstBranch cell) (secondBranch cell))

sumDifferenceSquares sumBranchSquares : List TensorDifferenceCell → ℚ
sumDifferenceSquares [] = 0ℚ
sumDifferenceSquares (cell ∷ cells) =
  L2.square (directDifference cell) + sumDifferenceSquares cells

sumBranchSquares [] = 0ℚ
sumBranchSquares (cell ∷ cells) =
  (L2.square (firstBranch cell) + L2.square (secondBranch cell))
  + sumBranchSquares cells

finiteTensorDifferenceSquareBound :
  (cells : List TensorDifferenceCell) →
  sumDifferenceSquares cells
  ≤ Error.two * sumBranchSquares cells
finiteTensorDifferenceSquareBound [] = ℚₚ.≤-refl
finiteTensorDifferenceSquareBound (cell ∷ cells) =
  let
    local = cellDifferenceSquareBound cell
    tail = finiteTensorDifferenceSquareBound cells
    summed = ℚₚ.+-mono-≤ local tail

    endpoint :
      Error.two
        * (L2.square (firstBranch cell) + L2.square (secondBranch cell))
        + Error.two * sumBranchSquares cells
      ≡ Error.two
        * ((L2.square (firstBranch cell) + L2.square (secondBranch cell))
          + sumBranchSquares cells)
    endpoint =
      solve
        ( L2.square (firstBranch cell)
        ∷ L2.square (secondBranch cell)
        ∷ sumBranchSquares cells
        ∷ [])
  in
  subst
    (λ upper →
      L2.square (directDifference cell) + sumDifferenceSquares cells
      ≤ upper)
    endpoint
    summed
