module DASHI.Physics.Closure.NSTriadKNAdversarialPrimitiveEstimates where

open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Bool using (Bool; false)

------------------------------------------------------------------------
-- Adversarial primitive-estimate surface.
--
-- The adversarial profile has a different target shape than forced-tail:
--
--   row    <= A_adv / N^2
--   column <= B_adv / N
--
-- so the product closes at N^-3 and therefore a fortiori at the Stage 3
-- threshold N^-2.

data AdversarialClass : Set where
  sparseAdmissible : AdversarialClass
  angularDegenerate : AdversarialClass
  boundarySmallShell : AdversarialClass

------------------------------------------------------------------------
-- Formula-level row/column count envelopes.
--
-- These are the classwise multiplicity formulas that the future concrete
-- adversarial incidence model must justify.

adversarialRowCountBound : AdversarialClass -> Nat -> Nat
adversarialRowCountBound sparseAdmissible _ = 1
adversarialRowCountBound angularDegenerate N = N
adversarialRowCountBound boundarySmallShell _ = 1

adversarialColumnCountBound : AdversarialClass -> Nat -> Nat
adversarialColumnCountBound sparseAdmissible N = N
adversarialColumnCountBound angularDegenerate N = N
adversarialColumnCountBound boundarySmallShell _ = 1

------------------------------------------------------------------------
-- Formula-level magnitude scales.
--
-- These are not yet arithmetic proofs; they are the explicit classwise
-- exponent choices that make the design equations visible:
--
--   row count exponent + row magnitude exponent <= -2
--   col count exponent + col magnitude exponent <= -1

adversarialRowMagnitudeScaleExponent : AdversarialClass -> Nat
adversarialRowMagnitudeScaleExponent sparseAdmissible = 2
adversarialRowMagnitudeScaleExponent angularDegenerate = 3
adversarialRowMagnitudeScaleExponent boundarySmallShell = 2

adversarialColumnMagnitudeScaleExponent : AdversarialClass -> Nat
adversarialColumnMagnitudeScaleExponent sparseAdmissible = 2
adversarialColumnMagnitudeScaleExponent angularDegenerate = 2
adversarialColumnMagnitudeScaleExponent boundarySmallShell = 1

------------------------------------------------------------------------
-- Primitive theorem obligations.
--
-- These are the actual next mathematical slots. They intentionally remain
-- uninhabited here.

postulate
  adversarialIncidenceClassified :
    (N : Nat) -> Set

  adversarialRowCountBoundObligated :
    (N : Nat) -> (c : AdversarialClass) -> Set

  adversarialColumnCountBoundObligated :
    (N : Nat) -> (c : AdversarialClass) -> Set

  adversarialMagnitudeEnvelopeObligated :
    (N : Nat) -> (c : AdversarialClass) -> Set

  adversarialRowProductN2BoundObligated :
    (N : Nat) -> (c : AdversarialClass) -> Set

  adversarialColumnProductN1BoundObligated :
    (N : Nat) -> (c : AdversarialClass) -> Set

------------------------------------------------------------------------
-- Status summary.
--
-- This is a progress surface only. No closure is claimed here.

record AdversarialPrimitiveEstimatesStatus : Set where
  constructor mkAdversarialPrimitiveEstimatesStatus
  field
    incidenceClassified : Bool
    rowCountBoundProved : Bool
    columnCountBoundProved : Bool
    magnitudeEnvelopeProved : Bool
    rowN2ProductProved : Bool
    columnN1ProductProved : Bool

open AdversarialPrimitiveEstimatesStatus public

currentAdversarialPrimitiveEstimatesStatus :
  AdversarialPrimitiveEstimatesStatus
currentAdversarialPrimitiveEstimatesStatus =
  mkAdversarialPrimitiveEstimatesStatus
    false
    false
    false
    false
    false
    false
