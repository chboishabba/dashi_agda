module Verification.JacobianNoninjectiveRegression where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- This module is deliberately a boundary/receipt surface.  The exact sparse-
-- polynomial expansion is executed by
-- scripts/check_jacobian_noninjective_example.py.  No kernel-level theorem
-- about the Jacobian conjecture is claimed here.

record ExactJacobianDiagnosticReceipt : Set where
  constructor receipt
  field
    ambientDimension       : Nat
    determinantConstant    : String
    determinantIdentityOK  : Bool
    distinctWitnessCount   : Nat
    commonImage            : String
    fibreWitnessesOK       : Bool
    kernelProofClaimed      : Bool

jacobianNoninjectiveExampleReceipt : ExactJacobianDiagnosticReceipt
jacobianNoninjectiveExampleReceipt =
  receipt
    3
    "-2"
    true
    3
    "(-1/4,0,0)"
    true
    false

-- Fail-closed interpretation boundary: this receipt records a checked exact
-- computation only.  It must not be promoted to a kernel proof or to a claim
-- resolving the complex Jacobian conjecture without reconciling the map's
-- stated hypotheses and provenance.
