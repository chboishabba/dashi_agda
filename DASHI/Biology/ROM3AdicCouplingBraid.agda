module DASHI.Biology.ROM3AdicCouplingBraid where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import DASHI.Algebra.BalancedTernary using (Trit; neg; zero; pos)
open import DASHI.Arithmetic.M9BraidPDA
open import DASHI.Arithmetic.M9MDLBraidEvaluation

------------------------------------------------------------------------
-- Minimal 6-of-3 coupling cell.
--
-- Every coupling carries a derived ternary triple and a real ternary triple.
-- This is the (3^3) × 2 carrier fixed in the thread; defect/projection are
-- downstream observations, not replacements for the paired object.

record Trit3 : Set where
  constructor trit3
  field
    elevation : Trit
    foreAft   : Trit
    rotation  : Trit
open Trit3 public

record Coupling63 : Set where
  constructor coupling63
  field
    derived : Trit3
    real    : Trit3
open Coupling63 public

record CouplingDefect : Set where
  constructor couplingDefect
  field
    source : Coupling63
    defect : Trit3
open CouplingDefect public

------------------------------------------------------------------------
-- π_A is an explicit forbidden-set projection; π_B carries history.

record PiAClassification : Set where
  constructor piAClassification
  field
    cell    : Coupling63
    outcome : Verdict
    forbiddenHyperface : Bool
open PiAClassification public

record PiBClassification : Set where
  constructor piBClassification
  field
    cell      : Coupling63
    state     : KernelState
    braidWord : BraidWord
    outcome   : Verdict
    burden    : Nat
open PiBClassification public

------------------------------------------------------------------------
-- Two interdependent couplings form the full six-coordinate defect surface.
-- It is not assumed separable: a legal discharge may require a crossing
-- between factor trees belonging to different coupling blocks.

record CouplingPair6D : Set where
  constructor couplingPair6D
  field
    firstCoupling  : Coupling63
    secondCoupling : Coupling63
open CouplingPair6D public

record CrossCouplingWitness (pair : CouplingPair6D) (s : KernelState) : Set where
  field
    firstFactor  : FactorCandidate
    secondFactor : FactorCandidate
    crossing     : CoupledWitness firstFactor secondFactor s
    jointContextAvailable : Bool
open CrossCouplingWitness public

record CoupledROMTransition : Set where
  constructor coupledROMTransition
  field
    before      : CouplingPair6D
    after       : CouplingPair6D
    stateBefore : KernelState
    stateAfter  : KernelState
    verdict     : Verdict
    mdlBurden   : Nat
open CoupledROMTransition public

------------------------------------------------------------------------
-- Full-body supervoxel surface.

record ROMSupervoxel : Set₁ where
  field
    couplings : List Coupling63
    pairwiseInterdependence : List CouplingPair6D
    braidTrace : BraidWord
    transitions : List CoupledROMTransition
    permissibilityBySurvival : Bool
    nativeThreeAdic : Bool
    noEuclideanGeometryClaim : Bool
    reading : String
open ROMSupervoxel public

record ROMPromotionBoundary (rom : ROMSupervoxel) : Set where
  field
    noCompleteHumanROMClaim : Bool
    noSMPLAxisCalibrationClaim : Bool
    noClinicalValidityClaim : Bool
    braidPDAKernelOnly : Bool
open ROMPromotionBoundary public

canonicalROMPromotionBoundary :
  (rom : ROMSupervoxel) → ROMPromotionBoundary rom
canonicalROMPromotionBoundary rom =
  record
    { noCompleteHumanROMClaim = true
    ; noSMPLAxisCalibrationClaim = true
    ; noClinicalValidityClaim = true
    ; braidPDAKernelOnly = true
    }
