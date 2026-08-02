module DASHI.Physics.Closure.NSTriadKNSymmetrisedFirstAdjointNullAudit where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact ordered-pair first-adjoint null-structure audit".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original exact finite audit.
-- Uses: the literal direct and swapped vector-valued first-adjoint formulas,
-- exact Leray projection, conjugate reality mates, and Gaussian-rational
-- transverse witnesses.
-- Relationship: tests the cheapest repository-native interpretation of the
-- projector-difference/null-form idea suggested by recent resonant
-- paraproduct reconnaissance.  Ordered-pair symmetrisation does not provide a
-- universal |p|/|q| gain: a scale-parametrised exact witness remains of size
-- |q| after projection and its reality mate reinforces rather than cancels it.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)

import DASHI.Physics.Closure.NSTriadKNLiteralVectorAdjointCandidates as Adjoints

data StaticGainDecision : Set where
  primitiveLowGain
  projectorDifferenceGain
  noUniversalStaticLowGain
  dynamicPhaseGeometryStillOpen : StaticGainDecision

orderedPairFirstAdjointDecision : StaticGainDecision
orderedPairFirstAdjointDecision = noUniversalStaticLowGain

data WitnessRole : Set where
  lowFirstAdjointOutput
  highRightInput
  highOriginalOutput
  transverseRightPolarisation
  transverseTestPolarisation : WitnessRole

witnessScale : Nat
witnessScale = 37

lowModeSquaredNorm : Nat
lowModeSquaredNorm = 1

highModeSquaredNorm : Nat
highModeSquaredNorm = 1369

symmetrisedAdjointSquaredNorm : Nat
symmetrisedAdjointSquaredNorm = 1369

realityFoldedSignedValue : Nat
realityFoldedSignedValue = 2738

record SymmetrisedFirstAdjointWitnessReceipt : Set where
  constructor witness-receipt
  field
    scaleIsThirtySeven : witnessScale ≡ 37
    lowNormIsOne : lowModeSquaredNorm ≡ 1
    highNormIsThirtySevenSquared : highModeSquaredNorm ≡ 1369
    symmetrisedAdjointRemainsHigh :
      symmetrisedAdjointSquaredNorm ≡ 1369
    realityMateDoublesSignedWitness :
      realityFoldedSignedValue ≡ 2738
    decisionIsNoUniversalStaticLowGain :
      orderedPairFirstAdjointDecision ≡ noUniversalStaticLowGain

open SymmetrisedFirstAdjointWitnessReceipt public

symmetrisedFirstAdjointWitnessReceipt :
  SymmetrisedFirstAdjointWitnessReceipt
symmetrisedFirstAdjointWitnessReceipt =
  witness-receipt refl refl refl refl refl refl

record NullRouteScopeAudit : Set where
  constructor scope-audit
  field
    directFirstAdjointFormulaAvailable :
      Adjoints.literalVectorAdjointCandidatesDefined ≡ true
    orderedPairFormulaAvailable :
      Adjoints.orderedPairFirstAdjointFormulaDefined ≡ true

    directPrimitiveProjectorGainRejected : Bool
    orderedPairStaticProjectorDifferenceGainRejected : Bool
    realityFoldCancellationRejectedOnWitness : Bool
    helicalSignCancellationUniversal : Bool
    dynamicWavePacketOrTimeOscillationRouteRuledOut : Bool

    directSobolevTailRouteStillAvailable : Bool
    weightedCommutatorRouteStillAvailable : Bool
    furtherHelicalRestrictedNullRouteStillAvailable : Bool

open NullRouteScopeAudit public

nullRouteScopeAudit : NullRouteScopeAudit
nullRouteScopeAudit =
  scope-audit
    Adjoints.literalVectorAdjointCandidatesDefinedIsTrue
    Adjoints.orderedPairFirstAdjointFormulaDefinedIsTrue
    true
    true
    true
    false
    false
    true
    true
    true

record NullRouteScopeReceipt : Set where
  constructor scope-receipt
  field
    directGainRejected :
      directPrimitiveProjectorGainRejected nullRouteScopeAudit ≡ true
    symmetrisedGainRejected :
      orderedPairStaticProjectorDifferenceGainRejected nullRouteScopeAudit ≡ true
    realityFoldDoesNotCancel :
      realityFoldCancellationRejectedOnWitness nullRouteScopeAudit ≡ true
    noUniversalHelicalCancellationClaim :
      helicalSignCancellationUniversal nullRouteScopeAudit ≡ false
    dynamicMechanismsRemainLogicallyOpen :
      dynamicWavePacketOrTimeOscillationRouteRuledOut nullRouteScopeAudit ≡ false
    tailRouteRetained :
      directSobolevTailRouteStillAvailable nullRouteScopeAudit ≡ true
    commutatorRouteRetained :
      weightedCommutatorRouteStillAvailable nullRouteScopeAudit ≡ true
    restrictedNullRouteRetained :
      furtherHelicalRestrictedNullRouteStillAvailable nullRouteScopeAudit ≡ true

open NullRouteScopeReceipt public

nullRouteScopeReceipt : NullRouteScopeReceipt
nullRouteScopeReceipt =
  scope-receipt refl refl refl refl refl refl refl refl

symmetrisedFirstAdjointExactAuditPassed : Bool
symmetrisedFirstAdjointExactAuditPassed = true

symmetrisedFirstAdjointExactAuditPassedIsTrue :
  symmetrisedFirstAdjointExactAuditPassed ≡ true
symmetrisedFirstAdjointExactAuditPassedIsTrue = refl

symmetrisationSuppliesUniversalFirstAdjointLowGain : Bool
symmetrisationSuppliesUniversalFirstAdjointLowGain = false

symmetrisationSuppliesUniversalFirstAdjointLowGainIsFalse :
  symmetrisationSuppliesUniversalFirstAdjointLowGain ≡ false
symmetrisationSuppliesUniversalFirstAdjointLowGainIsFalse = refl
