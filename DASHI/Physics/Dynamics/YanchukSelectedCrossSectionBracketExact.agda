{-# OPTIONS --safe #-}
module DASHI.Physics.Dynamics.YanchukSelectedCrossSectionBracketExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
import DASHI.Physics.Dynamics.BasinResolutionRobustnessExact as BRR

------------------------------------------------------------------------
-- Exact arithmetic owner for the selected finite-epsilon normal-form
-- cross-section used by scripts/check_singular_funnel_normal_form.py.
--
-- The numerical integrator supplies endpoint DESTINATION classifications.
-- This module owns only the exact bisection-grid arithmetic and the logical
-- promotion boundary.  In particular, it does not turn RK4 output into an
-- analytic ODE basin theorem.
------------------------------------------------------------------------

record ScaledPositiveCoordinate : Set where
  constructor scaledPositiveCoordinate
  field
    numerator : Nat
    denominator : Nat

open ScaledPositiveCoordinate public

record AdjacentScaledBracket : Set where
  constructor adjacentScaledBracket
  field
    lowerNumerator : Nat
    upperNumerator : Nat
    commonDenominator : Nat
    upperIsSuccessor :
      upperNumerator ≡ suc lowerNumerator

open AdjacentScaledBracket public

lowerCoordinate :
  AdjacentScaledBracket →
  ScaledPositiveCoordinate
lowerCoordinate B =
  scaledPositiveCoordinate
    (lowerNumerator B)
    (commonDenominator B)

upperCoordinate :
  AdjacentScaledBracket →
  ScaledPositiveCoordinate
upperCoordinate B =
  scaledPositiveCoordinate
    (upperNumerator B)
    (commonDenominator B)

record UnitGridWidth (B : AdjacentScaledBracket) : Set where
  constructor unitGridWidth
  field
    denominator : Nat
    denominatorAgrees :
      denominator ≡ commonDenominator B

open UnitGridWidth public

unitWidth :
  (B : AdjacentScaledBracket) →
  UnitGridWidth B
unitWidth B =
  unitGridWidth
    (commonDenominator B)
    refl

------------------------------------------------------------------------
-- Selected source fixture.
--
-- Starting bracket:
--   44 / 10^12  = 4.4e-11
--   45 / 10^12  = 4.5e-11
--
-- After sixteen midpoint classifications, the surviving adjacent dyadic-grid
-- points have common denominator 65536000000000000.
------------------------------------------------------------------------

selectedLowerNumerator : Nat
selectedLowerNumerator = 2933441

selectedUpperNumerator : Nat
selectedUpperNumerator = 2933442

selectedCommonDenominator : Nat
selectedCommonDenominator = 65536000000000000

selectedBracket : AdjacentScaledBracket
selectedBracket =
  adjacentScaledBracket
    selectedLowerNumerator
    selectedUpperNumerator
    selectedCommonDenominator
    refl

selectedBracketWidthIsOneGridUnit :
  UnitGridWidth selectedBracket
selectedBracketWidthIsOneGridUnit =
  unitWidth selectedBracket

selectedUpperIsSuccessor :
  selectedUpperNumerator ≡ suc selectedLowerNumerator
selectedUpperIsSuccessor = refl

------------------------------------------------------------------------
-- Numerical classification receipt.
--
-- The endpoint labels are data emitted by the independent RK4 diagnostic.
-- They remain source/diagnostic evidence.  The booleans below make the
-- promotion boundary machine-readable and prevent accidental theorem-level
-- interpretation of the endpoint classifications.
------------------------------------------------------------------------

data AttractorLabel : Set where
  lowerAttractor : AttractorLabel
  upperAttractor : AttractorLabel
  unresolvedAttractor : AttractorLabel

record SelectedCrossSectionNumericalReceipt : Set where
  constructor selectedCrossSectionNumericalReceipt
  field
    sourceDOI : String
    sourceRepository : String
    epsilonReading : String
    mu0Reading : String
    bracket : AdjacentScaledBracket
    lowerEndpointClassification : AttractorLabel
    upperEndpointClassification : AttractorLabel
    reducedBranchPrediction : AttractorLabel
    independentRK4Receipt : Bool
    finiteSelectedMismatchObserved : Bool
    analyticBasinTheoremProved : Bool
    globalWidthLawProved : Bool

open SelectedCrossSectionNumericalReceipt public

canonicalSelectedCrossSectionNumericalReceipt :
  SelectedCrossSectionNumericalReceipt
canonicalSelectedCrossSectionNumericalReceipt =
  selectedCrossSectionNumericalReceipt
    "10.1103/jtkh-9lz5"
    "https://github.com/hassanalkhayuon/Singular_Funnels"
    "epsilon = 0.1"
    "mu0 = 3.9"
    selectedBracket
    lowerAttractor
    upperAttractor
    upperAttractor
    true
    true
    false
    false

selectedReceiptDoesNotClaimAnalyticBasinTheorem :
  analyticBasinTheoremProved
    canonicalSelectedCrossSectionNumericalReceipt
  ≡ false
selectedReceiptDoesNotClaimAnalyticBasinTheorem = refl

selectedReceiptDoesNotClaimGlobalWidthLaw :
  globalWidthLawProved
    canonicalSelectedCrossSectionNumericalReceipt
  ≡ false
selectedReceiptDoesNotClaimGlobalWidthLaw = refl

selectedReceiptRecordsOppositeEndpointLabels :
  lowerEndpointClassification
      canonicalSelectedCrossSectionNumericalReceipt
    ≡ lowerAttractor
  ×
  upperEndpointClassification
      canonicalSelectedCrossSectionNumericalReceipt
    ≡ upperAttractor
selectedReceiptRecordsOppositeEndpointLabels =
  refl , refl
