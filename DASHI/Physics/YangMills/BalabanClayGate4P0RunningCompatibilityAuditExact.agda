module DASHI.Physics.YangMills.BalabanClayGate4P0RunningCompatibilityAuditExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.String using (String)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayGate4P0GrowthAbsorptionExact as P0
import DASHI.Physics.YangMills.BalabanClayGate4PolynomialSuppressionRecurrenceExact as Geometric

------------------------------------------------------------------------
-- Provenance and correction status.
--
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392. DOI: 10.1007/BF01238433.
--
-- The precise primary p0 definition, direction of the scale flow and constants
-- still require direct verification against the paper. The July 2026 v2 audit
-- of the Eriksson locator series is not theorem authority, but it correctly
-- retracts the earlier implication from a polylogarithmic p0 floor to a fixed
-- geometric factor in the scale index. This module records that correction as
-- a fail-closed compatibility boundary.
------------------------------------------------------------------------

data ScaleDecayRegime : Set where
  subPolynomial polynomial superPolynomial fixedRatioGeometric
  finiteWindowOnly unknownRegime : ScaleDecayRegime

record RunningSuppressionAudit : Set where
  constructor runningAudit
  field
    sourceOrDerivation : String
    inverseCouplingProfile : String
    p0Profile : String
    suppressionProfile : String
    resultingRegime : ScaleDecayRegime
    fixedRatioGeometricDerived : Bool
    sufficientForAllScaleGeometricAbsorption : Bool
    extraHypothesisRequired : Bool
    note : String

open RunningSuppressionAudit public

standardAffineInverseCouplingPolylogP0 : RunningSuppressionAudit
standardAffineInverseCouplingPolylogP0 = runningAudit
  "asymptotic-freedom proxy beta_k comparable to beta_0 + C k, with g_k comparable to beta_k^(-1/2)"
  "inverse coupling grows at most affinely in the scale index"
  "p0(g) comparable to A (log g^(-2))^theta"
  "exp(-c p0(g_k)) comparable to exp(-c A (log k)^theta)"
  superPolynomial
  false
  false
  true
  "for theta > 1 the decay beats every inverse power of k, but it remains slower than exp(-a k) for every fixed a > 0; theta = 1 is polynomial and theta < 1 is sub-polynomial"

powerLawPenaltyUpgrade : RunningSuppressionAudit
powerLawPenaltyUpgrade = runningAudit
  "additional H-P0 style power-law penalty, not derived from the polylog floor"
  "must be matched to the chosen RG direction and coupling convention"
  "p0 or the complete action penalty grows at least linearly in the scale index"
  "exp(-c p0(g_k)) admits a fixed-ratio geometric majorant"
  fixedRatioGeometric
  true
  true
  true
  "this is an additional analytic hypothesis until obtained from Bałaban's primary conventions or a new proof"

windowedSuppressionRoute : RunningSuppressionAudit
windowedSuppressionRoute = runningAudit
  "corrected finite weak-coupling window"
  "small-coupling control is available only through a finite scale cutoff"
  "the p0 profile is used pointwise inside the admissible window"
  "finite-window bounds do not imply an all-scale thermodynamic or continuum estimate"
  finiteWindowOnly
  false
  false
  true
  "useful for finite-volume estimates, insufficient for the all-volume continuum mass-gap chain"

record PolylogP0RunningData (Scale Scalar : Set) : Set₁ where
  field
    p0Growth : P0.P0SuperlinearLogGrowth Scale Scalar
    scaleRegime : ScaleDecayRegime
    regimeAudit : scaleRegime ≡ superPolynomial

open PolylogP0RunningData public

record GeometricAbsorptionUpgrade
    (Scale Scalar Bound : Set)
    (polylog : PolylogP0RunningData Scale Scalar) : Set₁ where
  field
    geometricStep : Geometric.PolynomialSuppressionStep Bound
    primaryOrNewAnalyticBridge : Set
    bridgeDoesNotFollowFromMetadataAlone : Set

open GeometricAbsorptionUpgrade public

record WindowedAbsorptionPackage
    (Scale Bound : Set) : Set₁ where
  field
    ScaleWithinWindow : Scale → Set
    largeFieldContribution smallFieldBudget : Scale → Bound
    LessEqual : Bound → Bound → Set
    absorbedInsideWindow : ∀ scale →
      ScaleWithinWindow scale →
      LessEqual (largeFieldContribution scale) (smallFieldBudget scale)

open WindowedAbsorptionPackage public

p0RunningRegimeAuditLevel : ProofLevel
p0RunningRegimeAuditLevel = machineChecked

polylogVersusGeometricInterfaceSeparationLevel : ProofLevel
polylogVersusGeometricInterfaceSeparationLevel = machineChecked

windowedAbsorptionVocabularyLevel : ProofLevel
windowedAbsorptionVocabularyLevel = machineChecked

powerLawOrGeometricUpgradeInputsLevel : ProofLevel
powerLawOrGeometricUpgradeInputsLevel = conditional

primaryP0ConventionVerificationLevel : ProofLevel
primaryP0ConventionVerificationLevel = conditional
