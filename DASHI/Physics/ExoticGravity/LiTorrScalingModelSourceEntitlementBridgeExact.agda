module DASHI.Physics.ExoticGravity.LiTorrScalingModelSourceEntitlementBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Interop.SourceAttributionShapePolicyExact as Shape
import DASHI.Physics.ExoticGravity.LiTorrTheorySourceDiligenceProofSearchExact as Diligence
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGScalingModelDiscriminatorExact as Scaling

------------------------------------------------------------------------
-- LI/TORR MODEL-FORM SOURCE ENTITLEMENT
--
-- A bibliographic candidate or DOI identity is not enough to authorize a
-- specific multiplicative scaling law.  Any imported model form must be tied
-- to an inspected source carrier, exact locator, bounded equation/model scope,
-- and the exact model-form object consumed by the discriminator.
------------------------------------------------------------------------

record LiTorrModelFormEntitlementReceipt : Set₁ where
  constructor li-torr-model-form-entitlement-receipt
  field
    sourceCandidate : Diligence.LiTorrTheorySourceCandidate
    attributedSource : Source.AttributedSource

    InspectedCarrierIdentityReceipt : Set
    inspectedCarrierIdentityReceipt : InspectedCarrierIdentityReceipt

    exactLocator : String
    ExactLocatorReceipt : Set
    exactLocatorReceipt : ExactLocatorReceipt

    boundedModelFormScope : String
    ModelFormScopeEntitlementReceipt : Set
    modelFormScopeEntitlementReceipt : ModelFormScopeEntitlementReceipt

    scalingModelClass : Scaling.ScalingModelClass
    scalingModelIsMultiplicativeConstitutive :
      scalingModelClass ≡ Scaling.multiplicativeConstitutiveCoefficient

    SameModelFormReceipt : Set
    sameModelFormReceipt : SameModelFormReceipt

open LiTorrModelFormEntitlementReceipt public

------------------------------------------------------------------------
-- Current in-repo candidates do not automatically inhabit this receipt.
------------------------------------------------------------------------

data CandidateAutomaticallyEntitlesScalingLaw : Set where

candidateMetadataDoesNotEntitleScalingLaw :
  CandidateAutomaticallyEntitlesScalingLaw → ⊥
candidateMetadataDoesNotEntitleScalingLaw ()

publishedModelAttributionShape : Shape.RequiredAttributionShape
publishedModelAttributionShape =
  Shape.requiredAttributionShape Shape.publishedScientificTheorem

record LiTorrScalingModelSourceBoundary : Set where
  constructor li-torr-scaling-model-source-boundary
  field
    doiIdentityAloneEntitlesExactScalingLaw : Bool
    registryStringAloneEntitlesExactScalingLaw : Bool
    inspectedCarrierRequired : Bool
    exactLocatorRequired : Bool
    boundedModelFormScopeRequired : Bool
    sameModelFormIdentityRequired : Bool
    sourceEntitlementProvesPhysicalModelCorrect : Bool
    sourceEntitlementProvesNegativeEffectiveG : Bool

canonicalLiTorrScalingModelSourceBoundary : LiTorrScalingModelSourceBoundary
canonicalLiTorrScalingModelSourceBoundary =
  li-torr-scaling-model-source-boundary
    false false true true true true false false
