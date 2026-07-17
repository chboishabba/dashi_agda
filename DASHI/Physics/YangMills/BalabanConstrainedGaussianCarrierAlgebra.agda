module DASHI.Physics.YangMills.BalabanConstrainedGaussianCarrierAlgebra where

-- Source-native operator disambiguation for the constrained Gaussian.
--
-- CMP 96 (2.154)--(2.156), CMP 99 (3.155)--(3.158), and CMP 109
-- (1.4), (2.10)--(2.13) use three different covariance-shaped operators:
--
--   1. Q A^-1 Q* is the covariance of the *constraint value*.  Its inverse is
--      the coarse Schur Hessian occurring in constrained minimisation.
--
--   2. (C_kerQ* A C_kerQ)^-1 is the covariance of the independent coordinates
--      after delta(Q B) is solved by B = C_kerQ Btilde.
--
--   3. C_kerQ (C_kerQ* A C_kerQ)^-1 C_kerQ* is the corresponding covariance
--      on the original constrained fluctuation carrier.
--
-- These operators must not be given one undifferentiated `C` name.  In
-- particular, the second and third objects are not Q A^-1 Q*.  This module
-- introduces no existence claim, determinant estimate, or source authority;
-- it only gives the literal compositions separate names.

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Physics.YangMills.BalabanNestedConstraintMinimum using
  ( _∘_
  ; constrainedCovariance
  )

-- Q A^-1 Q*: covariance transported to the constraint-value carrier.
constraintValueCovariance :
  {Field Constraint : Set} →
  (Field → Constraint) →
  (Field → Field) →
  (Constraint → Field) →
  Constraint → Constraint
constraintValueCovariance = constrainedCovariance

-- C_kerQ* A C_kerQ: Hessian in the independent coordinates used after
-- eliminating the dependent bond variables.
restrictedCoordinateHessian :
  {Field Coordinate : Set} →
  (Coordinate → Field) →
  (Field → Field) →
  (Field → Coordinate) →
  Coordinate → Coordinate
restrictedCoordinateHessian C-kerQ A C-kerQ* =
  C-kerQ* ∘ A ∘ C-kerQ

-- (C_kerQ* A C_kerQ)^-1: the covariance denoted C^(k) in CMP 109 p. 268
-- after the remaining variables have been renamed B.
independentCoordinateCovariance :
  {Field Coordinate : Set} →
  ((Coordinate → Coordinate) → Coordinate → Coordinate) →
  (Coordinate → Field) →
  (Field → Field) →
  (Field → Coordinate) →
  Coordinate → Coordinate
independentCoordinateCovariance inverseCoordinate C-kerQ A C-kerQ* =
  inverseCoordinate (restrictedCoordinateHessian C-kerQ A C-kerQ*)

-- C_kerQ (C_kerQ* A C_kerQ)^-1 C_kerQ*: covariance on the original
-- constrained fluctuation carrier, as in CMP 96 (2.156) and CMP 99 (3.157).
fullConstrainedFluctuationCovariance :
  {Field Coordinate : Set} →
  (Coordinate → Field) →
  (Coordinate → Coordinate) →
  (Field → Coordinate) →
  Field → Field
fullConstrainedFluctuationCovariance C-kerQ coordinateCovariance C-kerQ* =
  C-kerQ ∘ coordinateCovariance ∘ C-kerQ*

sourceFullCovarianceFromRestrictedHessian :
  {Field Coordinate : Set} →
  (inverseCoordinate :
    (Coordinate → Coordinate) → Coordinate → Coordinate) →
  (C-kerQ : Coordinate → Field) →
  (A : Field → Field) →
  (C-kerQ* : Field → Coordinate) →
  fullConstrainedFluctuationCovariance
    C-kerQ
    (independentCoordinateCovariance
      inverseCoordinate C-kerQ A C-kerQ*)
    C-kerQ*
  ≡ C-kerQ
      ∘ inverseCoordinate
          (restrictedCoordinateHessian C-kerQ A C-kerQ*)
      ∘ C-kerQ*
sourceFullCovarianceFromRestrictedHessian
  inverseCoordinate C-kerQ A C-kerQ* = refl
