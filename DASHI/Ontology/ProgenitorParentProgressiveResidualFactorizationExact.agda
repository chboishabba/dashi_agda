module DASHI.Ontology.ProgenitorParentProgressiveResidualFactorizationExact where

open import DASHI.Core.Prelude using (Bool; _≡_; refl)
import Data.Product as Product

import DASHI.Core.RecoverableQuotientCompositionExact as Recoverable

open import DASHI.Ontology.ProgenitorParentHyperfabric
open import DASHI.Ontology.ProgenitorParentProjectionFibre
open import DASHI.Ontology.ProgenitorParentResidualDynamicsExact using (levelFromParentSlot)

------------------------------------------------------------------------
-- Progressive residual factorisation.
--
-- Instead of treating the full RelationVector as one flat receipt, factor the
-- exact reopening through an intermediate semantic surface:
--
--   ParentCarrier
--      -> ParentSemanticSurface
--      -> WikidataParentSlot.
--
-- The first stage retains public-facing progenitor/genetic/genealogical
-- semantics and stores the remaining relation coordinates as its residual.
-- The second stage forgets those semantic coordinates to the Wikidata slot and
-- stores exactly them as its residual. RecoverableQuotientCompositionExact then
-- proves that the total residual is the product of the two stage residuals.
------------------------------------------------------------------------

record ParentSemanticSurface : Set where
  constructor parentSemanticSurface
  field
    semanticSlot : WikidataParentSlot
    semanticProgenitor : Bool
    semanticGenetic : Bool
    semanticGenealogicalParent : Bool
open ParentSemanticSurface public

record ParentPrivateResidual : Set where
  constructor parentPrivateResidual
  field
    privateGamete : Bool
    privateMitochondrial : Bool
    privateGestational : Bool
    privateIntendedParent : Bool
    privateLegalParent : Bool
    privateSocialParent : Bool
    privateCaregiver : Bool
    privateIdentityKnown : Bool
    privateIdentityDisclosable : Bool
open ParentPrivateResidual public

projectSemanticSurface : ParentCarrier → ParentSemanticSurface
projectSemanticSurface carrier =
  parentSemanticSurface
    (projectParentSlot carrier)
    (progenitorRelation relationValue)
    (geneticContributor relationValue)
    (genealogicalParent relationValue)
  where
  relationValue : RelationVector
  relationValue = carrierRelation carrier

privateResidual : ParentCarrier → ParentPrivateResidual
privateResidual carrier =
  parentPrivateResidual
    (gameteContributor relationValue)
    (mitochondrialContributor relationValue)
    (gestationalContributor relationValue)
    (intendedParent relationValue)
    (legalParent relationValue)
    (socialParent relationValue)
    (caregiver relationValue)
    (identityKnown relationValue)
    (identityDisclosable relationValue)
  where
  relationValue : RelationVector
  relationValue = carrierRelation carrier

reopenSemanticSurface :
  ParentSemanticSurface → ParentPrivateResidual → ParentCarrier
reopenSemanticSurface surface residual =
  parentCarrier
    (levelFromParentSlot (semanticSlot surface))
    (relationVector
      (semanticProgenitor surface)
      (semanticGenetic surface)
      (privateGamete residual)
      (privateMitochondrial residual)
      (privateGestational residual)
      (semanticGenealogicalParent surface)
      (privateIntendedParent residual)
      (privateLegalParent residual)
      (privateSocialParent residual)
      (privateCaregiver residual)
      (privateIdentityKnown residual)
      (privateIdentityDisclosable residual))

semanticStageReopensExactly :
  (carrier : ParentCarrier) →
  reopenSemanticSurface
    (projectSemanticSurface carrier)
    (privateResidual carrier)
  ≡ carrier
semanticStageReopensExactly (parentCarrier individualLevel relationValue) = refl
semanticStageReopensExactly (parentCarrier lineageLevel relationValue) = refl

parentToSemanticRecoverable :
  Recoverable.ExactRecoverableProjection ParentCarrier ParentSemanticSurface
parentToSemanticRecoverable =
  Recoverable.exactRecoverableProjection
    ParentPrivateResidual
    projectSemanticSurface
    privateResidual
    reopenSemanticSurface
    semanticStageReopensExactly

------------------------------------------------------------------------
-- Second stage: semantic surface -> Wikidata slot.
------------------------------------------------------------------------

record ParentSemanticResidual : Set where
  constructor parentSemanticResidual
  field
    residualProgenitor : Bool
    residualGenetic : Bool
    residualGenealogicalParent : Bool
open ParentSemanticResidual public

projectSemanticToSlot : ParentSemanticSurface → WikidataParentSlot
projectSemanticToSlot = semanticSlot

semanticResidual : ParentSemanticSurface → ParentSemanticResidual
semanticResidual surface =
  parentSemanticResidual
    (semanticProgenitor surface)
    (semanticGenetic surface)
    (semanticGenealogicalParent surface)

reopenSemanticFromSlot :
  WikidataParentSlot → ParentSemanticResidual → ParentSemanticSurface
reopenSemanticFromSlot slotValue residual =
  parentSemanticSurface
    slotValue
    (residualProgenitor residual)
    (residualGenetic residual)
    (residualGenealogicalParent residual)

semanticToSlotReopensExactly :
  (surface : ParentSemanticSurface) →
  reopenSemanticFromSlot
    (projectSemanticToSlot surface)
    (semanticResidual surface)
  ≡ surface
semanticToSlotReopensExactly
  (parentSemanticSurface slotValue progenitorValue geneticValue parentValue) = refl

semanticToSlotRecoverable :
  Recoverable.ExactRecoverableProjection ParentSemanticSurface WikidataParentSlot
semanticToSlotRecoverable =
  Recoverable.exactRecoverableProjection
    ParentSemanticResidual
    projectSemanticToSlot
    semanticResidual
    reopenSemanticFromSlot
    semanticToSlotReopensExactly

------------------------------------------------------------------------
-- Composite quotient.
------------------------------------------------------------------------

parentProgressiveRecoverable :
  Recoverable.ExactRecoverableProjection ParentCarrier WikidataParentSlot
parentProgressiveRecoverable =
  Recoverable.composeRecoverable
    parentToSemanticRecoverable
    semanticToSlotRecoverable

parentCompositeResidualIsProduct :
  Recoverable.Residual parentProgressiveRecoverable
  ≡ Product._×_ ParentPrivateResidual ParentSemanticResidual
parentCompositeResidualIsProduct =
  Recoverable.compositeResidualIsProduct
    parentToSemanticRecoverable
    semanticToSlotRecoverable

parentProgressiveReopeningExact :
  (carrier : ParentCarrier) →
  Recoverable.reopen parentProgressiveRecoverable
    (Recoverable.project parentProgressiveRecoverable carrier)
    (Recoverable.residual parentProgressiveRecoverable carrier)
  ≡ carrier
parentProgressiveReopeningExact =
  Recoverable.reopenExact parentProgressiveRecoverable

------------------------------------------------------------------------
-- The quotient tower therefore does not need one ever-widening public record.
-- Each refinement level retains only the residual introduced at that stage.
------------------------------------------------------------------------

record ParentProgressiveResidualBoundary : Set where
  constructor parentProgressiveResidualBoundary
  field
    semanticStageExactlyRecoverable : Bool
    semanticStageExactlyRecoverableIsTrue :
      semanticStageExactlyRecoverable ≡ true
    publicSlotStageExactlyRecoverable : Bool
    publicSlotStageExactlyRecoverableIsTrue :
      publicSlotStageExactlyRecoverable ≡ true
    compositeResidualFactorsByStage : Bool
    compositeResidualFactorsByStageIsTrue :
      compositeResidualFactorsByStage ≡ true

canonicalParentProgressiveResidualBoundary : ParentProgressiveResidualBoundary
canonicalParentProgressiveResidualBoundary =
  parentProgressiveResidualBoundary true refl true refl true refl true refl
