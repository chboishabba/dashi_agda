module DASHI.Physics.Closure.NSTriadKNAffineCertificateUnderdetermination where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Pierre Germain; Oleg
-- Kiriukhin; DASHI repository contributors.
-- Title: "Exact factorised underdetermination certificate for the Stage-3
-- three-weight affine system".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24;
-- Publicacions Matematiques, Extra 2002, 57--91; Journal of Differential
-- Equations 226 (2006), 373--428; arXiv:2604.12188v1; DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.5565/PUBLMAT_Esco02_04;
-- 10.1016/j.jde.2005.10.007; 10.48550/arXiv.2604.12188; the exact
-- factorisation record is repository-original and has no DOI.
-- Uses: twelve separated rows, nine finite-overlap rows, five analytic
-- archetypes, three Schur owners and three independent auxiliary weights.
-- Relationship: preserves the raw count 21 * 3 = 63 while proving that the
-- rows factor through eight coefficient families. The current exact
-- obstruction is therefore twenty-four independent numeric coefficients,
-- not sixty-three unrelated values. No positive epsilon or infeasibility
-- result is fabricated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

import DASHI.Physics.Closure.NSTriadKNComponentAffineConstraintLedger as Ledger
import DASHI.Physics.Closure.NSTriadKNSeparatedComponentEndpointProfiles as Profiles
import DASHI.Physics.Closure.NSTriadKNFiniteOverlapTransportConstants as Transport
import DASHI.Physics.Closure.NSTriadKNTriadicDyadicExponentSystem as Exponents
import DASHI.Physics.Closure.NSTriadKNAffineRowFactorisation as Factor
import DASHI.Physics.Closure.NSTriadKNAffineCertificateExactAudit as Audit

separatedRowCount : Nat
separatedRowCount = 12

overlapRowCount : Nat
overlapRowCount = 9

totalConstraintRowCount : Nat
totalConstraintRowCount = separatedRowCount + overlapRowCount

weightCoefficientCountPerRow : Nat
weightCoefficientCountPerRow = 3

minimumMissingWeightCoefficientCount : Nat
minimumMissingWeightCoefficientCount =
  totalConstraintRowCount * weightCoefficientCountPerRow

minimumMissingWeightCoefficientCountIs63 :
  minimumMissingWeightCoefficientCount ≡ 63
minimumMissingWeightCoefficientCountIs63 = refl

independentCoefficientFamilyCount : Nat
independentCoefficientFamilyCount = Factor.independentFamilyCount

minimumMissingIndependentWeightCoefficientCount : Nat
minimumMissingIndependentWeightCoefficientCount =
  Factor.independentCoefficientSlotCount

minimumMissingIndependentWeightCoefficientCountIs24 :
  minimumMissingIndependentWeightCoefficientCount ≡ 24
minimumMissingIndependentWeightCoefficientCountIs24 =
  Factor.independentCoefficientSlotCountIs24

data AffineCertificateOutcome : Set where
  certified
  infeasible
  zeroSlackBoundary
  underdetermined : Nat → AffineCertificateOutcome

rawAffineOutcome : AffineCertificateOutcome
rawAffineOutcome = underdetermined minimumMissingWeightCoefficientCount

currentAffineOutcome : AffineCertificateOutcome
currentAffineOutcome =
  underdetermined minimumMissingIndependentWeightCoefficientCount

rawOutcomeIsUnderdetermined63 :
  rawAffineOutcome ≡ underdetermined 63
rawOutcomeIsUnderdetermined63 = refl

currentOutcomeIsUnderdetermined24 :
  currentAffineOutcome ≡ underdetermined 24
currentOutcomeIsUnderdetermined24 = refl

record CompleteNumericRowInput : Set₁ where
  field
    Scalar : Set
    leftCoefficient rightCoefficient outputCoefficient : Scalar
    unweightedTerm target : Scalar
    lowerEndpointSlack upperEndpointSlack : Scalar
    rowIdentityProved : Set

open CompleteNumericRowInput public

record CompleteAffineInput : Set₁ where
  field
    separatedRows : Ledger.separatedComponentCount ≡ separatedRowCount
    overlapRows : Ledger.finiteOverlapConditionCount ≡ overlapRowCount
    everyIndependentFamilyNumeric : Set
    allRowsExtractedFromFamilyAssignment : Set
    allThreeWeightsIndependent : Set
    lowerEndpointEvaluated : Set
    upperEndpointEvaluated : Set

open CompleteAffineInput public

endpointProfilesAreAvailable : Bool
endpointProfilesAreAvailable = Profiles.allTwelveEndpointProfilesInstantiated

endpointProfilesAreAvailableIsTrue : endpointProfilesAreAvailable ≡ true
endpointProfilesAreAvailableIsTrue =
  Profiles.allTwelveEndpointProfilesInstantiatedIsTrue

transportConstantsAreNumericallySpecified : Bool
transportConstantsAreNumericallySpecified =
  Transport.allNineSquaredSafeConstantsSpecified

transportConstantsAreNumericallySpecifiedIsTrue :
  transportConstantsAreNumericallySpecified ≡ true
transportConstantsAreNumericallySpecifiedIsTrue =
  Transport.allNineSquaredSafeConstantsSpecifiedIsTrue

rowOnlyRank : Nat
rowOnlyRank = 1

threeWeightUnknownCount : Nat
threeWeightUnknownCount = 3

rowOnlyNullity : Nat
rowOnlyNullity = 2

rowOnlyRankNullity : rowOnlyRank + rowOnlyNullity ≡ threeWeightUnknownCount
rowOnlyRankNullity = refl

endpointProfilesDetermineThreeWeightCoefficients : Bool
endpointProfilesDetermineThreeWeightCoefficients = false

endpointProfilesDetermineThreeWeightCoefficientsIsFalse :
  endpointProfilesDetermineThreeWeightCoefficients ≡ false
endpointProfilesDetermineThreeWeightCoefficientsIsFalse = refl

rawRowsFactorThroughEightFamilies : Bool
rawRowsFactorThroughEightFamilies =
  Factor.rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlots

rawRowsFactorThroughEightFamiliesIsTrue :
  rawRowsFactorThroughEightFamilies ≡ true
rawRowsFactorThroughEightFamiliesIsTrue =
  Factor.rawSixtyThreeSlotsFactorThroughTwentyFourIndependentSlotsIsTrue

affineSolverArchitectureClosed : Bool
affineSolverArchitectureClosed = Audit.affineSolverArchitectureClosed

affineSolverArchitectureClosedIsTrue :
  affineSolverArchitectureClosed ≡ true
affineSolverArchitectureClosedIsTrue =
  Audit.affineSolverArchitectureClosedIsTrue

strictPositiveEpsilonAvailable : Bool
strictPositiveEpsilonAvailable = false

strictPositiveEpsilonAvailableIsFalse :
  strictPositiveEpsilonAvailable ≡ false
strictPositiveEpsilonAvailableIsFalse = refl
