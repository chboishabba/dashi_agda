module DASHI.Physics.Closure.NSTriadKNAffineCertificateUnderdetermination where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: Loukas Grafakos; Rodolfo H. Torres; Pierre Germain; Oleg
-- Kiriukhin; DASHI repository contributors.
-- Title: "Exact underdetermination certificate for the Stage-3 three-weight
-- affine system".
-- Venue/year: Journal of Functional Analysis 187 (2001), 1--24;
-- Publicacions Matematiques, Extra 2002, 57--91; Journal of Differential
-- Equations 226 (2006), 373--428; arXiv:2604.12188v1; DASHI formal
-- development, 2026.
-- DOI: 10.1006/jfan.2001.3804; 10.5565/PUBLMAT_Esco02_04;
-- 10.1016/j.jde.2005.10.007; 10.48550/arXiv.2604.12188; the exact obstruction
-- record is repository-original and has no DOI.
-- Uses: twelve separated components, nine finite-overlap conditions, three
-- independent auxiliary weights and the existing row-only rank-one audit.
-- Relationship: implements the attachment's fail-closed contingency. The
-- endpoint decay profiles do not contain the three leg coefficients required
-- by an affine constraint, so no epsilon is fabricated. The solver outcome is
-- explicitly "underdetermined" until all 21 coefficient rows are populated.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; _*_; _+_)

import DASHI.Physics.Closure.NSTriadKNComponentAffineConstraintLedger as Ledger
import DASHI.Physics.Closure.NSTriadKNSeparatedComponentEndpointProfiles as Profiles
import DASHI.Physics.Closure.NSTriadKNFiniteOverlapTransportConstants as Transport
import DASHI.Physics.Closure.NSTriadKNTriadicDyadicExponentSystem as Exponents

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

data AffineCertificateOutcome : Set where
  certified
  infeasible
  underdetermined : Nat → AffineCertificateOutcome

currentAffineOutcome : AffineCertificateOutcome
currentAffineOutcome = underdetermined minimumMissingWeightCoefficientCount

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
    everySeparatedRowNumeric : Set
    everyOverlapRowNumeric : Set
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

strictPositiveEpsilonAvailable : Bool
strictPositiveEpsilonAvailable = false

strictPositiveEpsilonAvailableIsFalse :
  strictPositiveEpsilonAvailable ≡ false
strictPositiveEpsilonAvailableIsFalse = refl

currentOutcomeIsUnderdetermined :
  currentAffineOutcome ≡ underdetermined 63
currentOutcomeIsUnderdetermined = refl
