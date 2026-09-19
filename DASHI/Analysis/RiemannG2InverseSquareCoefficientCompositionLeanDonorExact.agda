module DASHI.Analysis.RiemannG2InverseSquareCoefficientCompositionLeanDonorExact where

------------------------------------------------------------------------
-- THEOREM-BEARING LEAN DONOR FOR THE R2 INVERSE-SQUARE COEFFICIENT CUT
--
-- The companion Lean branch now source-writes:
--
--   inverseSquare_threeChannel_lt_cluster
--
--     near <= cNear/t^2
--     far <= cFar/t^2
--     gamma <= cGamma/t^2
--     cCluster/t^2 <= cluster
--     cNear + cFar + cGamma < cCluster
--     --------------------------------
--     near + far + gamma < cluster
--
-- and the quartic far-shell specialization
--
--   cFar = 144*A,
--
-- using the already-written quartic far theorem.
--
-- This Agda owner records exact source custody and the mathematical recut.  It
-- does NOT pretend the Lean theorem has been transported into the Agda kernel.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

record R2InverseSquareLeanDonorReceipt : Set where
  constructor r2-inverse-square-lean-donor-receipt
  field
    repository : String
    branch : String
    sourcePath : String
    regressionPath : String
    genericTheorem : String
    quarticFarSpecialization : String
    farShellDependency : String
    genericSourceCommit : String
    regressionSourceCommit : String

open R2InverseSquareLeanDonorReceipt public

currentR2InverseSquareLeanDonorReceipt : R2InverseSquareLeanDonorReceipt
currentR2InverseSquareLeanDonorReceipt =
  r2-inverse-square-lean-donor-receipt
    "chboishabba/dashi_lean4"
    "agent/rh-farshell-quartic-bypass"
    "Synthesis/RiemannR2InverseSquareCoefficientComposition.lean"
    "Synthesis/RiemannR2InverseSquareCoefficientCompositionRegression.lean"
    "Synthesis.inverseSquare_threeChannel_lt_cluster"
    "Synthesis.quarticFar_threeChannel_lt_cluster"
    "Synthesis.farShell_quartic_le_inverseSquare"
    "94d9c13edfd1b9a0614256bce903d3f373ac68a3"
    "6eacdac984af5f2873377f9289544b8f088c2016"

record R2InverseSquareCoefficientCut : Set where
  constructor r2-inverse-square-coefficient-cut
  field
    nearInverseSquareCoefficientRequired : Bool
    quarticFarInverseSquareCoefficientOwned : Bool
    quarticFarCoefficientIs144TimesA : Bool
    gammaInverseSquareCoefficientRequired : Bool
    actualClusterInverseSquareLowerCoefficientRequired : Bool
    strictCoefficientSlackRequired : Bool

    genericCoefficientCompositionSourceWrittenInLean : Bool
    genericCoefficientCompositionTransportedIntoAgda : Bool
    quarticSpecializationSourceWrittenInLean : Bool
    quarticSpecializationTransportedIntoAgda : Bool

    directR2FollowsAfterTransportAndRateInputs : Bool
    directR2InhabitedHere : Bool
    rhDerivedHere : Bool

open R2InverseSquareCoefficientCut public

canonicalR2InverseSquareCoefficientCut : R2InverseSquareCoefficientCut
canonicalR2InverseSquareCoefficientCut =
  r2-inverse-square-coefficient-cut
    true
    true
    true
    true
    true
    true
    true
    false
    true
    false
    true
    false
    false
