module DASHI.Physics.Closure.NSTriadKNLuoGalerkinInteractionDifferenceExact where

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
-- Replace an uninterpreted interaction-approximation error by the exact
-- two-term Galerkin difference decomposition. If
--
--   N(u)   = B(u,u) . u_q,
--   N(u_N) = B(u_N,u_N) . (u_N)_q,
--
-- then at the scalar norm-carrier level
--
--   N(u)-N(u_N)
--     = (B(u,u)-B(u_N,u_N)) . u_q
--       + B(u_N,u_N) . (u_q-(u_N)_q).
--
-- The module proves the radical-free squared estimate
--
--   |N-N_N|^2
--     <= 2 (nonlinearError * physicalBlockBound
--           + approximationNonlinearBound * blockError).
--
-- Thus the remaining analytic producer is precisely the pair of nonlinear
-- and block projection errors, not a free interaction-error sequence.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _-_; _≤_; nonNegative)
import Data.Rational.Properties as ℚₚ
open ℚₚ using (_≤?_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; sym)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as L2

two : ℚ
two = Int.+ 2 / 1

twoNonnegative : 0ℚ ≤ two
twoNonnegative = toWitness {a? = 0ℚ ≤? two} _

interaction : ℚ → ℚ → ℚ
interaction nonlinear block = nonlinear * block

interactionDifferenceIdentity :
  (physicalNonlinear approximationNonlinear
   physicalBlock approximationBlock : ℚ) →
  interaction physicalNonlinear physicalBlock
    - interaction approximationNonlinear approximationBlock
  ≡ (physicalNonlinear - approximationNonlinear) * physicalBlock
    + approximationNonlinear * (physicalBlock - approximationBlock)
interactionDifferenceIdentity
  physicalNonlinear approximationNonlinear
  physicalBlock approximationBlock =
  solve
    ( physicalNonlinear ∷ approximationNonlinear
    ∷ physicalBlock ∷ approximationBlock ∷ [])

squareSumBound :
  (left right : ℚ) →
  L2.square (left + right)
  ≤ two * (L2.square left + L2.square right)
squareSumBound left right =
  let
    defectNN = L2.squareNonnegative (left - right)

    addDefect :
      L2.square (left + right)
      ≤ L2.square (left + right) + L2.square (left - right)
    addDefect =
      subst
        (λ lower →
          lower
          ≤ L2.square (left + right) + L2.square (left - right))
        (ℚₚ.+-identityʳ (L2.square (left + right)))
        (ℚₚ.+-monoʳ-≤ (L2.square (left + right)) defectNN)

    identity :
      L2.square (left + right) + L2.square (left - right)
      ≡ two * (L2.square left + L2.square right)
    identity = solve (left ∷ right ∷ [])
  in
  subst
    (λ upper → L2.square (left + right) ≤ upper)
    identity
    addDefect

squareProductMeaning :
  (left right : ℚ) →
  L2.square (left * right)
  ≡ L2.square left * L2.square right
squareProductMeaning left right = solve (left ∷ right ∷ [])

record GalerkinInteractionDifferenceData : Set where
  constructor galerkin-interaction-difference-data
  field
    physicalNonlinear approximationNonlinear : ℚ
    physicalBlock approximationBlock : ℚ

    nonlinearError blockError : ℚ
    physicalBlockBound approximationNonlinearBound : ℚ

    nonlinearErrorNonnegative : 0ℚ ≤ nonlinearError
    blockErrorNonnegative : 0ℚ ≤ blockError
    physicalBlockBoundNonnegative : 0ℚ ≤ physicalBlockBound
    approximationNonlinearBoundNonnegative :
      0ℚ ≤ approximationNonlinearBound

    nonlinearDifferenceBound :
      L2.square (physicalNonlinear - approximationNonlinear)
      ≤ nonlinearError

    physicalBlockSquareBound :
      L2.square physicalBlock ≤ physicalBlockBound

    approximationNonlinearSquareBound :
      L2.square approximationNonlinear
      ≤ approximationNonlinearBound

    blockDifferenceBound :
      L2.square (physicalBlock - approximationBlock)
      ≤ blockError

open GalerkinInteractionDifferenceData public

interactionDifferenceSquared :
  GalerkinInteractionDifferenceData → ℚ
interactionDifferenceSquared dataSet =
  L2.square
    ( interaction
        (physicalNonlinear dataSet)
        (physicalBlock dataSet)
      - interaction
        (approximationNonlinear dataSet)
        (approximationBlock dataSet))

interactionDifferenceSquaredBound :
  (dataSet : GalerkinInteractionDifferenceData) →
  interactionDifferenceSquared dataSet
  ≤ two
    * ( nonlinearError dataSet * physicalBlockBound dataSet
      + approximationNonlinearBound dataSet * blockError dataSet)
interactionDifferenceSquaredBound dataSet =
  let
    firstTerm =
      (physicalNonlinear dataSet - approximationNonlinear dataSet)
      * physicalBlock dataSet

    secondTerm =
      approximationNonlinear dataSet
      * (physicalBlock dataSet - approximationBlock dataSet)

    splitSquare :
      interactionDifferenceSquared dataSet
      ≡ L2.square (firstTerm + secondTerm)
    splitSquare =
      cong L2.square
        (interactionDifferenceIdentity
          (physicalNonlinear dataSet)
          (approximationNonlinear dataSet)
          (physicalBlock dataSet)
          (approximationBlock dataSet))

    pairSquare = squareSumBound firstTerm secondTerm

    firstProductBound :
      L2.square firstTerm
      ≤ nonlinearError dataSet * physicalBlockBound dataSet
    firstProductBound =
      subst
        (λ lower →
          lower
          ≤ nonlinearError dataSet * physicalBlockBound dataSet)
        (sym
          (squareProductMeaning
            (physicalNonlinear dataSet - approximationNonlinear dataSet)
            (physicalBlock dataSet)))
        (L2.nonnegativeProductMonotone
          (L2.squareNonnegative
            (physicalNonlinear dataSet - approximationNonlinear dataSet))
          (L2.squareNonnegative (physicalBlock dataSet))
          (nonlinearErrorNonnegative dataSet)
          (physicalBlockBoundNonnegative dataSet)
          (nonlinearDifferenceBound dataSet)
          (physicalBlockSquareBound dataSet))

    secondProductBound :
      L2.square secondTerm
      ≤ approximationNonlinearBound dataSet * blockError dataSet
    secondProductBound =
      subst
        (λ lower →
          lower
          ≤ approximationNonlinearBound dataSet * blockError dataSet)
        (sym
          (squareProductMeaning
            (approximationNonlinear dataSet)
            (physicalBlock dataSet - approximationBlock dataSet)))
        (L2.nonnegativeProductMonotone
          (L2.squareNonnegative (approximationNonlinear dataSet))
          (L2.squareNonnegative
            (physicalBlock dataSet - approximationBlock dataSet))
          (approximationNonlinearBoundNonnegative dataSet)
          (blockErrorNonnegative dataSet)
          (approximationNonlinearSquareBound dataSet)
          (blockDifferenceBound dataSet))

    sumProducts =
      ℚₚ.+-mono-≤ firstProductBound secondProductBound

    scaledProducts :
      two * (L2.square firstTerm + L2.square secondTerm)
      ≤ two
        * ( nonlinearError dataSet * physicalBlockBound dataSet
          + approximationNonlinearBound dataSet * blockError dataSet)
    scaledProducts =
      let instance twoNN = nonNegative twoNonnegative
      in ℚₚ.*-monoˡ-≤-nonNeg two sumProducts
  in
  subst
    (λ lower →
      lower
      ≤ two
        * ( nonlinearError dataSet * physicalBlockBound dataSet
          + approximationNonlinearBound dataSet * blockError dataSet))
    (sym splitSquare)
    (ℚₚ.≤-trans pairSquare scaledProducts)
