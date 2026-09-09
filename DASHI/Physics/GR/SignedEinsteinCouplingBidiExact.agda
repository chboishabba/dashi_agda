module DASHI.Physics.GR.SignedEinsteinCouplingBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)

import DASHI.Physics.Laws.GravityCosmologyLaws as Laws
import DASHI.Physics.Closure.GRWeakFieldPredictionReceipt as Weak

------------------------------------------------------------------------
-- SIGNED EINSTEIN/NEWTON COUPLING AS A COUNTERFACTUAL BIDI
--
-- This owner does not assert that the physical Newton constant is negative.
-- It exposes the sign coordinate already implicit in an Einstein coupling and
-- asks what a pure sign flip does when source, geometry conventions, probe and
-- leading weak-field approximation are held fixed.
------------------------------------------------------------------------

data CouplingSign : Set where
  positiveCoupling : CouplingSign
  zeroCoupling : CouplingSign
  negativeCoupling : CouplingSign

flipCouplingSign : CouplingSign → CouplingSign
flipCouplingSign positiveCoupling = negativeCoupling
flipCouplingSign zeroCoupling = zeroCoupling
flipCouplingSign negativeCoupling = positiveCoupling

flipCouplingSignInvolutive :
  (sign : CouplingSign) → flipCouplingSign (flipCouplingSign sign) ≡ sign
flipCouplingSignInvolutive positiveCoupling = refl
flipCouplingSignInvolutive zeroCoupling = refl
flipCouplingSignInvolutive negativeCoupling = refl

data SourceResponseOrientation : Set where
  ordinarySourceOrientation : SourceResponseOrientation
  decoupledSourceOrientation : SourceResponseOrientation
  reversedSourceOrientation : SourceResponseOrientation

responseOrientation : CouplingSign → SourceResponseOrientation
responseOrientation positiveCoupling = ordinarySourceOrientation
responseOrientation zeroCoupling = decoupledSourceOrientation
responseOrientation negativeCoupling = reversedSourceOrientation

couplingSignFromOrientation : SourceResponseOrientation → CouplingSign
couplingSignFromOrientation ordinarySourceOrientation = positiveCoupling
couplingSignFromOrientation decoupledSourceOrientation = zeroCoupling
couplingSignFromOrientation reversedSourceOrientation = negativeCoupling

couplingOrientationBidiForward :
  (sign : CouplingSign) →
  couplingSignFromOrientation (responseOrientation sign) ≡ sign
couplingOrientationBidiForward positiveCoupling = refl
couplingOrientationBidiForward zeroCoupling = refl
couplingOrientationBidiForward negativeCoupling = refl

couplingOrientationBidiReverse :
  (orientation : SourceResponseOrientation) →
  responseOrientation (couplingSignFromOrientation orientation) ≡ orientation
couplingOrientationBidiReverse ordinarySourceOrientation = refl
couplingOrientationBidiReverse decoupledSourceOrientation = refl
couplingOrientationBidiReverse reversedSourceOrientation = refl

------------------------------------------------------------------------
-- LEADING WEAK-FIELD SIGN SURFACE
--
-- The existing GR baseline owner displays four first weak-field corrections
-- proportional to G.  Under a deliberately frozen source/geometry counterfactual
-- their correction sign therefore follows the coupling sign.  This is not a
-- theorem about a globally re-solved negative-G Solar System.
------------------------------------------------------------------------

data LeadingCorrectionOrientation : Set where
  conventionalCorrection : LeadingCorrectionOrientation
  noLeadingCorrection : LeadingCorrectionOrientation
  reversedCorrection : LeadingCorrectionOrientation

leadingCorrectionOrientation :
  CouplingSign → Weak.GRWeakFieldObservable → LeadingCorrectionOrientation
leadingCorrectionOrientation positiveCoupling observable = conventionalCorrection
leadingCorrectionOrientation zeroCoupling observable = noLeadingCorrection
leadingCorrectionOrientation negativeCoupling observable = reversedCorrection

data NegativeGWeakFieldReading : Set where
  retrogradePerihelionCorrection : NegativeGWeakFieldReading
  oppositeLightDeflection : NegativeGWeakFieldReading
  shapiroTimeAdvance : NegativeGWeakFieldReading
  gravitationalBlueshift : NegativeGWeakFieldReading

negativeGReading : Weak.GRWeakFieldObservable → NegativeGWeakFieldReading
negativeGReading Weak.mercuryPerihelionAdvance = retrogradePerihelionCorrection
negativeGReading Weak.solarLimbLightDeflection = oppositeLightDeflection
negativeGReading Weak.solarShapiroDelayScale = shapiroTimeAdvance
negativeGReading Weak.solarSurfaceGravitationalRedshift = gravitationalBlueshift

negativeGReversesEveryDisplayedLeadingCorrection :
  (observable : Weak.GRWeakFieldObservable) →
  leadingCorrectionOrientation negativeCoupling observable ≡ reversedCorrection
negativeGReversesEveryDisplayedLeadingCorrection observable = refl

zeroGRemovesEveryDisplayedLeadingCorrection :
  (observable : Weak.GRWeakFieldObservable) →
  leadingCorrectionOrientation zeroCoupling observable ≡ noLeadingCorrection
zeroGRemovesEveryDisplayedLeadingCorrection observable = refl

------------------------------------------------------------------------
-- FROZEN SIGN PROBE VERSUS SELF-CONSISTENT THEORY
------------------------------------------------------------------------

record FrozenSignedCouplingProbe : Set where
  constructor frozen-signed-coupling-probe
  field
    sign : CouplingSign
    weakFieldBaseline : Weak.GRWeakFieldPredictionReceipt
    sourceHeldFixed : Bool
    geometryConventionHeldFixed : Bool
    probeHeldFixed : Bool
    leadingOrderOnly : Bool

open FrozenSignedCouplingProbe public

canonicalNegativeGFrozenProbe : FrozenSignedCouplingProbe
canonicalNegativeGFrozenProbe = frozen-signed-coupling-probe
  negativeCoupling
  Weak.canonicalGRWeakFieldPredictionReceipt
  true true true true

data SelfConsistentNegativeGResidual : Set where
  missingSignedEinsteinLawRealisation : SelfConsistentNegativeGResidual
  missingNegativeGCoupledInitialValueProblem : SelfConsistentNegativeGResidual
  missingReSolvedMetricAndGeodesics : SelfConsistentNegativeGResidual
  missingReSolvedMatterAndSourceDynamics : SelfConsistentNegativeGResidual
  missingWeakFieldErrorControlForNegativeCoupling : SelfConsistentNegativeGResidual

record SignedEinsteinCouplingBoundary : Set where
  constructor signed-einstein-coupling-boundary
  field
    ordinaryEinsteinLawAlreadyHasCouplingCoordinate : Bool
    negativeCouplingIsAssertedPhysicalHere : Bool
    frozenSignFlipReversesDisplayedLeadingCorrections : Bool
    frozenSignProbeEqualsSelfConsistentNegativeGTheory : Bool
    negativeGEqualsNegativeMass : Bool
    negativeGEqualsNegativeStressEnergy : Bool
    negativeGAutomaticallyPreservesBoundOrbitBackground : Bool
    negativeGAutomaticallyValidatesAntigravity : Bool
    selfConsistentNegativeGRequiresReSolvingDynamics : Bool

canonicalSignedEinsteinCouplingBoundary : SignedEinsteinCouplingBoundary
canonicalSignedEinsteinCouplingBoundary =
  signed-einstein-coupling-boundary
    true false true false false false false false true

------------------------------------------------------------------------
-- Reuse marker: the signed fibre is attached to the existing abstract GR law;
-- no second Einstein-equation architecture is introduced here.
------------------------------------------------------------------------

record SignedEinsteinLawProbe (law : Laws.EinsteinGravityLaw) : Set₁ where
  constructor signed-einstein-law-probe
  field
    couplingSign : CouplingSign
    usesExistingCouplingCarrier : Laws.EinsteinGravityLaw.Coupling law → Set
    FrozenSignAdequacy : Set
    frozenSignAdequacy : FrozenSignAdequacy
