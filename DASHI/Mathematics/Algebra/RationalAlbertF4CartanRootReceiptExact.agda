module DASHI.Mathematics.Algebra.RationalAlbertF4CartanRootReceiptExact where

------------------------------------------------------------------------
-- CARTAN / CHIRALITY RECEIPT FOR THE RATIONAL ALBERT DERIVATION ALGEBRA
--
-- Companion exact producers:
--   scripts/albert_inner_derivation_rank.py
--   scripts/albert_triality_cartan_probe.py
--
-- Four commuting inner derivations
--
--   [L_x0,L_x1], [L_x2,L_x3], [L_x4,L_x5], [L_x6,L_x7]
--
-- form the coordinate Cartan chosen inside the exact 28-dimensional so8
-- sector.  Their action distinguishes the three 8-dimensional triality roles:
--
-- * first octonion slot: vector 8, standard four orthogonal plane rotations;
-- * second slot: half-spin 8 with H_k^2 = -1/4 I and chirality +1;
-- * third slot: half-spin 8 with H_k^2 = -1/4 I and chirality -1.
--
-- Hence the root/weight ledger is
--
--   24 D4 roots + 8 vector + 8 spin+ + 8 spin- = 48,
--   4 Cartan + 48 roots = 52 derivation dimensions.
--
-- Companion Lean independently constructs the corresponding standard F4 root
-- datum and proves its simple-reflection Weyl closure has order 1152.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record CartanTrialityReceipt : Set where
  constructor cartan-triality-receipt
  field
    scriptPath : String
    cartanDimension : Nat
    cartanGeneratorsAreInnerDerivations : Bool
    cartanGeneratorsCommuteExactly : Bool
    vectorRoleDimension : Nat
    spinPlusRoleDimension : Nat
    spinMinusRoleDimension : Nat
    vectorPlaneRotationPatternExact : Bool
    spinCartanSquareMinusQuarterIdentityExact : Bool
    spinPlusChiralityPositiveExact : Bool
    spinMinusChiralityNegativeExact : Bool
    d4RootCount : Nat
    vectorWeightCount : Nat
    spinPlusWeightCount : Nat
    spinMinusWeightCount : Nat
    totalRootCount : Nat
    totalDerivationDimension : Nat
open CartanTrialityReceipt public

canonicalCartanTrialityReceipt : CartanTrialityReceipt
canonicalCartanTrialityReceipt =
  cartan-triality-receipt
    "scripts/albert_triality_cartan_probe.py"
    4
    true
    true
    8
    8
    8
    true
    true
    true
    true
    24
    8
    8
    8
    48
    52

record CrossKernelF4RootReceipt : Set where
  constructor cross-kernel-f4-root-receipt
  field
    companionLeanRootCount48Paid : Bool
    companionLeanLong24Short24Paid : Bool
    companionLeanTrialityEightEightEightPaid : Bool
    companionLeanF4CartanMatrixPaid : Bool
    companionLeanWeylOrder1152Paid : Bool
    companionLeanClosureFixedPointPaid : Bool
    literalComplexWeightEigenvectorIntertwinerPaid : Bool
open CrossKernelF4RootReceipt public

canonicalCrossKernelF4RootReceipt : CrossKernelF4RootReceipt
canonicalCrossKernelF4RootReceipt =
  cross-kernel-f4-root-receipt true true true true true true false

record Boundary : Set where
  constructor boundary
  field
    exactCartanFourPaid : Bool
    vectorSpinSpinRolesPaid : Bool
    exactFortyEightRootLedgerPaid : Bool
    exactFiftyTwoDimensionLedgerPaid : Bool
    finiteF4RootDatumAvailableCrossKernel : Bool
    complexifiedWeightSpaceBijectionPaid : Bool
    fullF4AutomorphismGroupSchemePaid : Bool
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true true true true true false false
