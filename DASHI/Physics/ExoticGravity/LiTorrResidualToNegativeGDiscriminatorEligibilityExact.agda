module DASHI.Physics.ExoticGravity.LiTorrResidualToNegativeGDiscriminatorEligibilityExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.LiTorrOrdinaryConfounderResidualRouterExact as Router
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGDiscriminatorCutsetExact as Cutset
import DASHI.Interop.SourceAttributionShapePolicyExact as Shape

------------------------------------------------------------------------
-- SURVIVING RESIDUAL -> MECHANISM-DISCRIMINATOR ELIGIBILITY
--
-- Clearing the ordinary-confounder gate does not prove exotic gravity.  It
-- only makes the residual eligible to enter the existing DASHI discriminator
-- cutset, where source amplitude and material regime must be varied
-- independently and replication/model-class separation remain mandatory.
------------------------------------------------------------------------

record DiscriminatorEligibilityInput (d : SI.Dimension) : Set₂ where
  constructor discriminator-eligibility-input
  field
    routing : Router.SourceAttributedResidualRouting d
    routingDecisionIsEligible :
      Router.decision routing ≡ Router.eligibleForMechanismDiscriminator
    sourceRolesRetained : Bool
    ordinaryConfounderBundleSameObject : Bool
    eligibilityRevision : String

open DiscriminatorEligibilityInput public

record DiscriminatorEligibilityReceipt (d : SI.Dimension) : Set₂ where
  constructor discriminator-eligibility-receipt
  field
    input : DiscriminatorEligibilityInput d
    requiredCutset : Cutset.MaterialEffectiveNegativeGCutset
    cutsetIsCanonical : requiredCutset ≡ Cutset.canonicalMaterialEffectiveNegativeGCutset
    eligibleForSourceAmplitudeSweep : Bool
    eligibleForMaterialRegimeSweep : Bool
    eligibleForReplicationDesign : Bool
    physicalNegativeGEstablished : Bool
    historicalAuthorEndorsementCreated : Bool

open DiscriminatorEligibilityReceipt public

compileDiscriminatorEligibility :
  {d : SI.Dimension} →
  DiscriminatorEligibilityInput d →
  DiscriminatorEligibilityReceipt d
compileDiscriminatorEligibility input =
  discriminator-eligibility-receipt
    input
    Cutset.canonicalMaterialEffectiveNegativeGCutset
    refl
    true true true false false

attributionShape : Shape.RequiredAttributionShape
attributionShape = Shape.requiredAttributionShape Shape.internalDerivedTheorem

record ResidualToDiscriminatorBoundary : Set where
  constructor residual-to-discriminator-boundary
  field
    confounderSurvivalEqualsNegativeG : Bool
    eligibilityEqualsDiscriminationReceipt : Bool
    sourceAmplitudeSweepStillRequired : Bool
    materialRegimeSweepStillRequired : Bool
    modelClassSeparationStillRequired : Bool
    independentReplicationStillRequired : Bool
    internalBridgeMayBeAttributedToAmyOrLiTorr : Bool

canonicalResidualToDiscriminatorBoundary : ResidualToDiscriminatorBoundary
canonicalResidualToDiscriminatorBoundary =
  residual-to-discriminator-boundary
    false false true true true true false
