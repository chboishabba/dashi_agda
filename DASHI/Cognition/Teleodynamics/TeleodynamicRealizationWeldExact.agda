module DASHI.Cognition.Teleodynamics.TeleodynamicRealizationWeldExact where

------------------------------------------------------------------------
-- SEMANTIC ACTION EQUIVARIANCE != TARGET-DOMAIN REALIZATION
--
-- Reuses the merged relation/representation realization owner.  Even a latent
-- representation that transforms equivariantly under declared semantic
-- interventions needs a separate commuting decoder before it realizes a
-- target-domain phenomenon.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.SemanticInterventionEquivarianceExact as Intervention
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization

record EquivariantAndRealized
    (Fine Output Representation Target : Set)
    (model : Fine → Output)
    (intervention : Intervention.SemanticIntervention Fine Output)
    (targetPhenomenon : Fine → Target) : Set₁ where
  constructor equivariant-and-realized
  field
    representationEquivariance :
      Intervention.RepresentationEquivariance
        {Fine} {Output} {Representation} model intervention
    targetRealization :
      Realization.RepresentationRealizationWitness
        (Intervention.RepresentationEquivariance.encode representationEquivariance)
        targetPhenomenon
    justification : String

open EquivariantAndRealized public

record TeleodynamicRealizationWeldBoundary : Set where
  constructor teleodynamic-realization-weld-boundary
  field
    semanticActionEquivarianceCreatesTargetRealization : Bool
    heldOutCompositionCreatesTargetRealization : Bool
    futureLanguageAgreementCreatesTargetRealization : Bool
    targetRealizationRequiresCommutingWitness : Bool
    targetRealizationCreatesPhenomenalIdentity : Bool
    targetRealizationCreatesPhysicalCoupling : Bool
    targetRealizationCreatesNormativeAuthority : Bool

canonicalRealizationWeldBoundary : TeleodynamicRealizationWeldBoundary
canonicalRealizationWeldBoundary =
  teleodynamic-realization-weld-boundary
    false false false true false false false

------------------------------------------------------------------------
-- Attribution:
-- * realization witness architecture is reused from merged DASHI PR #632;
-- * semantic intervention equivariance is reused from the geometric-reasoning
--   donor tranche;
-- * their composition here is DASHI integration work.
------------------------------------------------------------------------
