module DASHI.Physics.YangMills.BalabanClayGate4ROperationDecayTargetsExact where

open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Exact analytic targets for Gate 4.
--
-- Primary authority:
-- Tadeusz Bałaban,
-- "Large Field Renormalization. II. Localization, Exponentiation, and Bounds
-- for the R Operation", Communications in Mathematical Physics 122 (1989),
-- 355--392, DOI: 10.1007/BF01238433.
--
-- Target locations in the primary paper:
--   * equation (1.89), p. 387: localized T-operation small factor;
--   * equation (1.100), p. 388: polymer decay for R^(k)(X);
--   * Theorem 1, p. 388: preservation of the inductive parameters.
--
-- Lluis Eriksson, "Interface Lemmas for the Multiscale Proof of the Lattice
-- Yang--Mills Mass Gap" (viXra:2602.0052v1, February 2026, no DOI) is recorded
-- only as an unreviewed locator for these equation numbers and for a proposed
-- absorption argument.  It is not an admissible theorem authority.
------------------------------------------------------------------------

record BalabanTOperationSmallFactorTarget
    (Scale Component Bound : Set) : Set₁ where
  field
    TWeight : Scale → Component → Bound
    p0Suppression : Scale → Bound
    LessEqual : Bound → Bound → Set
    tOperationSmallFactor : ∀ scale component →
      LessEqual (TWeight scale component) (p0Suppression scale)

open BalabanTOperationSmallFactorTarget public

record BalabanROperationPolymerDecayTarget
    (Scale Polymer BoundaryCondition RExpression Bound : Set) : Set₁ where
  field
    RActivity : Scale → Polymer → BoundaryCondition → RExpression
    norm : RExpression → Bound
    p0Suppression : Scale → Bound
    diameterDecay : Scale → Polymer → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    rOperationDecayUniformInBoundary : ∀ scale polymer boundary →
      LessEqual
        (norm (RActivity scale polymer boundary))
        (multiply (p0Suppression scale) (diameterDecay scale polymer))

open BalabanROperationPolymerDecayTarget public

record BalabanLargeFieldAbsorptionTarget
    (Scale Bound : Set) : Set₁ where
  field
    residualMagnitudeSquared : Scale → Bound
    largeFieldSuppression : Scale → Bound
    smallFieldScaleGain : Scale → Bound
    multiply : Bound → Bound → Bound
    LessEqual : Bound → Bound → Set

    largeFieldAbsorbedBySmallFieldBudget : ∀ scale →
      LessEqual
        (multiply (residualMagnitudeSquared scale)
          (largeFieldSuppression scale))
        (smallFieldScaleGain scale)

open BalabanLargeFieldAbsorptionTarget public

record BalabanCombinedGate4AnalyticTarget
    (Scale Polymer BoundaryCondition RExpression Bound : Set) : Set₁ where
  field
    rDecay : BalabanROperationPolymerDecayTarget
      Scale Polymer BoundaryCondition RExpression Bound
    absorption : BalabanLargeFieldAbsorptionTarget Scale Bound
    admissibleCouplingDomainPreserved : Set
    boundaryTermsShareUniformAnalyticityDomain : Set
    combinedPolymerNormCloses : Set

open BalabanCombinedGate4AnalyticTarget public

tOperationSmallFactorTargetLevel : ProofLevel
tOperationSmallFactorTargetLevel = conditional

rOperationPolymerDecayTargetLevel : ProofLevel
rOperationPolymerDecayTargetLevel = conditional

largeFieldAbsorptionTargetLevel : ProofLevel
largeFieldAbsorptionTargetLevel = conditional

combinedGate4AnalyticTargetLevel : ProofLevel
combinedGate4AnalyticTargetLevel = conditional
