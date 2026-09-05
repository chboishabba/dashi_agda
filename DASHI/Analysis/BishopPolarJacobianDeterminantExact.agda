module DASHI.Analysis.BishopPolarJacobianDeterminantExact where

import Real as Bishop
import RealProperties as BishopP

------------------------------------------------------------------------
-- BISHOP-REAL POLAR JACOBIAN DETERMINANT
--
-- The older polar determinant owner is rational.  This theorem lives directly
-- on the Bishop setoid carrier used by the Casimir trigonometric lane.
------------------------------------------------------------------------

square : Bishop.ℝ → Bishop.ℝ
square x = Bishop._*_ x x

bishopPolarDeterminant : Bishop.ℝ → Bishop.ℝ → Bishop.ℝ → Bishop.ℝ
bishopPolarDeterminant radius cosine sine =
  Bishop._-_
    (Bishop._*_ cosine (Bishop._*_ radius cosine))
    (Bishop._*_
      (Bishop.-_ (Bishop._*_ radius sine))
      sine)

polarDeterminantIsRadiusTimesPythagorean :
  ∀ radius cosine sine →
  Bishop._≃_
    (bishopPolarDeterminant radius cosine sine)
    (Bishop._*_
      radius
      (Bishop._+_ (square cosine) (square sine)))
polarDeterminantIsRadiusTimesPythagorean radius cosine sine =
  let open BishopP.ℝ-Solver in
  solve 3
    (λ r c s →
      (c ⊗ (r ⊗ c)) ⊖ ((⊝ (r ⊗ s)) ⊗ s)
      ⊜ r ⊗ ((c ⊗ c) ⊕ (s ⊗ s)))
    BishopP.≃-refl radius cosine sine

polarDeterminantIsRadius :
  ∀ radius cosine sine →
  Bishop._≃_
    (Bishop._+_ (square sine) (square cosine))
    Bishop.1ℝ →
  Bishop._≃_
    (bishopPolarDeterminant radius cosine sine)
    radius
polarDeterminantIsRadius radius cosine sine pythagorean =
  let
    cosineFirst :
      Bishop._≃_
        (Bishop._+_ (square cosine) (square sine))
        Bishop.1ℝ
    cosineFirst =
      BishopP.≃-trans
        (BishopP.+-comm (square cosine) (square sine))
        pythagorean
  in
  BishopP.≃-trans
    (polarDeterminantIsRadiusTimesPythagorean radius cosine sine)
    (BishopP.≃-trans
      (BishopP.*-cong BishopP.≃-refl cosineFirst)
      (BishopP.*-identityʳ radius))

record Status : Set where
  field
    bishopCarrierDeterminantAlgebraOwned : Bool
    pythagoreanToRadiusCompilerOwned : Bool

    bishopCarrierDeterminantAlgebraOwnedIsTrue :
      bishopCarrierDeterminantAlgebraOwned ≡ true
    pythagoreanToRadiusCompilerOwnedIsTrue :
      pythagoreanToRadiusCompilerOwned ≡ true

open Status public

canonicalStatus : Status
canonicalStatus = record
  { bishopCarrierDeterminantAlgebraOwned = true
  ; pythagoreanToRadiusCompilerOwned = true
  ; bishopCarrierDeterminantAlgebraOwnedIsTrue = refl
  ; pythagoreanToRadiusCompilerOwnedIsTrue = refl
  }
