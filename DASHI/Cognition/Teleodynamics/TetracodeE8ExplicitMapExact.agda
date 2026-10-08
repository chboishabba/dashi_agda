module DASHI.Cognition.Teleodynamics.TetracodeE8ExplicitMapExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- DASHI synthesis over a standard external tetracode/Eisenstein E8
-- construction.  The executable producer is
-- scripts/check_tetracode_e8_explicit_map.py.
--
-- This owner records exactly what that audit establishes and keeps the
-- five-trit 240-carrier recognition problem separate.
------------------------------------------------------------------------

record TetracodeE8ExecutionReceipt : Set where
  constructor tetracodeE8ExecutionReceipt
  field
    tetracodeWordCount : Nat
    nonzeroWeightThreeWordCount : Nat
    zeroResidueMinimalCount : Nat
    nonzeroResidueMinimalCount : Nat
    eisensteinMinimalShellCount : Nat
    standardIntegerRootCount : Nat
    standardHalfRootCount : Nat
    standardTotalRootCount : Nat
    explicitMatrixImageIsInjective : Bool
    explicitMatrixImageEqualsStandardE8RootSet : Bool
    gramSpectrumMatchesE8RootSpectrum : Bool
    pythonExecutionIsKernelProof : Bool

open TetracodeE8ExecutionReceipt public

canonicalTetracodeE8ExecutionReceipt : TetracodeE8ExecutionReceipt
canonicalTetracodeE8ExecutionReceipt =
  tetracodeE8ExecutionReceipt
    9 8 24 216 240 112 128 240
    true true true false

record ExplicitE8MapObligations : Set where
  constructor explicitE8MapObligations
  field
    eisensteinCarrierFormalized : Bool
    tetracodeMembershipFormalized : Bool
    normThreeShellFormalized : Bool
    matrixMapFormalized : Bool
    imageEqualityKernelProved : Bool
    sourceAttributionRetained : Bool

open ExplicitE8MapObligations public

canonicalExplicitE8MapObligations : ExplicitE8MapObligations
canonicalExplicitE8MapObligations =
  explicitE8MapObligations false false false false false true

record Boundary : Set where
  constructor boundary
  field
    tetracodeConstructsActualE8RootSetExecutable : Bool
    explicitMapIsOnlyCardinalityMatching : Bool
    explicitMapClosesLilaRootEnumerationAtExecutionLayer : Bool
    explicitMapIdentifiesRelativeT5Carrier : Bool
    relativeT5StillNeedsIndependentRecognition : Bool
    executionAuditTransfersScientificAuthorship : Bool

open Boundary public

canonicalBoundary : Boundary
canonicalBoundary =
  boundary true false true false true false

executionCountRegression :
  eisensteinMinimalShellCount canonicalTetracodeE8ExecutionReceipt ≡ 240
executionCountRegression = refl

explicitImageRegression :
  explicitMatrixImageEqualsStandardE8RootSet canonicalTetracodeE8ExecutionReceipt ≡ true
explicitImageRegression = refl

relativeT5NonPromotionRegression :
  explicitMapIdentifiesRelativeT5Carrier canonicalBoundary ≡ false
relativeT5NonPromotionRegression = refl
