module Verification.JacobianNoninjectiveRegression where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

open import Verification.JacobianCounterexampleKernel as Kernel
  using
    ( ¬_
    ; Injective
    ; F
    ; F-notInjective
    ; JacobianConjectureDimension3
    ; jacobianConjectureDimension3False
    ; JacobianConjectureDimensionThreePlus
    ; jacobianConjectureDimensionThreePlusFalse
    )
open import DASHI.Provenance.AIAssistedMathematicsProvenance as Provenance

-- Public attribution
-- ------------------
-- This concrete polynomial map was publicly announced by Levent Alpöge on
-- 20 July 2026.  His announcement credited Akhil Mathew for asking about the
-- problem and Fable for producing the example.  DASHI attributes the public
-- mathematical announcement to Alpöge and does not claim discovery priority.
--
-- scripts/check_jacobian_noninjective_example.py remains an independent exact
-- executable regression.  Verification.JacobianCounterexampleKernel now also
-- defines the polynomial syntax, differentiates it, normalises the determinant
-- with Agda's rational ring tactic, checks the rational fibre, proves
-- noninjectivity, packages a Keller map, refutes the dimension-three statement,
-- and pads the counterexample by untouched coordinates.

record ExactJacobianCounterexampleReceipt : Set where
  constructor receipt
  field
    publicAnnouncer : String
    announcementDate : String
    creditedQuestioner : String
    creditedSystem : String
    ambientDimension : Nat
    determinantConstant : String
    externalExactRegressionChecked : Bool
    kernelPolynomialSyntaxChecked : Bool
    kernelSymbolicDifferentiationChecked : Bool
    kernelJacobianIdentityChecked : Bool
    distinctWitnessCount : Nat
    commonImage : String
    kernelFibreWitnessesChecked : Bool
    kernelCollisionProofChecked : Bool
    kernelNoninjectivityChecked : Bool
    jacobianConjectureDimension3Refuted : Bool
    identityPaddingAllDimensionsAtLeast3Checked : Bool
    dimensionTwoAffected : Bool
    dimensionTwoAffectedIsFalse : dimensionTwoAffected ≡ false
    propernessOrMonodromyClaimed : Bool
    propernessOrMonodromyClaimedIsFalse :
      propernessOrMonodromyClaimed ≡ false

alpogeJacobianCounterexampleReceipt : ExactJacobianCounterexampleReceipt
alpogeJacobianCounterexampleReceipt =
  receipt
    "Levent Alpöge"
    "2026-07-20"
    "Akhil Mathew"
    "Fable"
    3
    "-2"
    true
    true
    true
    true
    3
    "(-1/4,0,0)"
    true
    true
    true
    true
    true
    false
    refl
    false
    refl

-- Kernel-level consequence exports.

alpogeMapNotInjective : ¬ Injective F
alpogeMapNotInjective = F-notInjective

jacobianConjectureDimension3Refutation :
  ¬ JacobianConjectureDimension3
jacobianConjectureDimension3Refutation =
  jacobianConjectureDimension3False

paddedRefutation :
  (extraCoordinates : Nat) →
  ¬ (JacobianConjectureDimensionThreePlus extraCoordinates)
paddedRefutation = jacobianConjectureDimensionThreePlusFalse

provenance : Provenance.DiscoveryProvenance
provenance = Provenance.alpogeFableProvenance

-- Interpretation boundary
-- -----------------------
-- The counterexample itself is now kernel-checked at the polynomial,
-- differentiation, determinant, collision and logical-consequence levels.
-- Properness, generic fibre degree, monodromy and topology at infinity are
-- separate global analyses.  The three-variable construction and its identity
-- padding do not settle the independent dimension-two problem.
