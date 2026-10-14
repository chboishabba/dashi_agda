module DASHI.Reasoning.AlbertF4LeanCubicNormRigidityReceiptExact where

open import Agda.Builtin.Bool using (Bool; true; false)

------------------------------------------------------------------------
-- CROSS-PROVER RECEIPT ONLY
--
-- Companion Lean #52 now source-writes on the literal rational Albert carrier:
--
-- * quadratic adjoint and bilinear trace;
-- * (x#)# = N(x)x;
-- * exact cubic polarization / gradient identity;
-- * 1 × x = T(x)1 - x;
-- * exact Jordan-product recovery from (N,#,T,1);
-- * positive-definite/nondegenerate trace pairing;
-- * source-written norm+unit rigidity compiler upgrading a Q-linear norm
--   symmetry fixing 1 to adjoint/cross/Jordan preservation.
--
-- This file records that development state without importing Lean kernel
-- authority into Agda.  Agda's own rational Albert, derivation and split-F4
-- results remain independently authoritative.
------------------------------------------------------------------------

record Boundary : Set where
  constructor boundary
  field
    nativeCubicNormStructureSourceWritten : Bool
    adjointIdentitySourceWritten : Bool
    cubicPolarizationSourceWritten : Bool
    jordanRecoverySourceWritten : Bool
    tracePairNondegeneracySourceWritten : Bool
    normUnitRigiditySourceWritten : Bool
    unitStabilizerJordanEqualityStructurallyReduced : Bool
    abstractF4GroupTypeStillClassificationLevel : Bool
    crossKernelProofAuthorityTransferred : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true true true true false
