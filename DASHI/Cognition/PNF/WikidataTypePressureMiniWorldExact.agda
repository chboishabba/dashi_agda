module DASHI.Cognition.PNF.WikidataTypePressureMiniWorldExact where

------------------------------------------------------------------------
-- FINITE WIKIDATA / TYPE-PRESSURE REPAIR MINI-WORLD
--
-- The declared ontology and the relational role evidence are kept separate.
-- When they disagree, the bounded repair endpoint underspecifies rather than
-- silently replacing one asserted type with another.  This is the concrete
-- finite regression for:
--
--   wrongly specific < correctly underspecified.
--
-- It is a DASHI toy world, not a claim about a particular live Wikidata item.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Cognition.PNF.WikidataRepairProposal as Repair

------------------------------------------------------------------------
-- A node is currently declared as one ontology role while predicate
-- participation supplies pressure toward another role.
------------------------------------------------------------------------

data EventType : Set where
  eventSeries : EventType
  eventEdition : EventType
  typeUnderspecified : EventType

data PredicateRoleEvidence : Set where
  editionParticipation : PredicateRoleEvidence
  seriesParticipation : PredicateRoleEvidence

data TypePressureDirection : Set where
  pressureSeries : TypePressureDirection
  pressureEdition : TypePressureDirection

rolePressure : PredicateRoleEvidence → TypePressureDirection
rolePressure editionParticipation = pressureEdition
rolePressure seriesParticipation = pressureSeries

data DeclaredRoleMismatch : EventType → PredicateRoleEvidence → Set where
  seriesDeclaredEditionObserved :
    DeclaredRoleMismatch eventSeries editionParticipation
  editionDeclaredSeriesObserved :
    DeclaredRoleMismatch eventEdition seriesParticipation

------------------------------------------------------------------------
-- Repair policy: contradiction authorizes a review proposal, not automatic
-- replacement.  Underspecification is the conservative endpoint until an
-- independent promotion proof is supplied.
------------------------------------------------------------------------

repairForMismatch :
  ∀ {declared evidence} →
  DeclaredRoleMismatch declared evidence → Repair.RepairOperation
repairForMismatch seriesDeclaredEditionObserved = Repair.underspecifyType
repairForMismatch editionDeclaredSeriesObserved = Repair.underspecifyType

seriesEditionMismatchUnderspecifies :
  repairForMismatch seriesDeclaredEditionObserved ≡ Repair.underspecifyType
seriesEditionMismatchUnderspecifies = refl

editionSeriesMismatchUnderspecifies :
  repairForMismatch editionDeclaredSeriesObserved ≡ Repair.underspecifyType
editionSeriesMismatchUnderspecifies = refl

------------------------------------------------------------------------
-- Latent type remains a proposal coordinate rather than a replacement truth.
------------------------------------------------------------------------

data LatentTypeCandidate : Set where
  latentEdition : LatentTypeCandidate
  latentSeries : LatentTypeCandidate

record OntologyResidual : Set where
  constructor ontologyResidual
  field
    declaredType : EventType
    observedRole : PredicateRoleEvidence
    latentCandidate : LatentTypeCandidate

open OntologyResidual public

mismatchResidual : OntologyResidual
mismatchResidual =
  ontologyResidual eventSeries editionParticipation latentEdition

data ResidualPromotesLatentType : OntologyResidual → Set where

residualCannotPromoteLatentType :
  ResidualPromotesLatentType mismatchResidual → ⊥
residualCannotPromoteLatentType ()

------------------------------------------------------------------------
-- Explicit comparison of repair endpoints.
------------------------------------------------------------------------

data RepairSafetyOrder : Repair.RepairOperation → Repair.RepairOperation → Set where
  underspecificationPreferredToUnsupportedPromotion :
    RepairSafetyOrder Repair.proposeLatentType Repair.underspecifyType

conservativeRepairOrdering :
  RepairSafetyOrder Repair.proposeLatentType Repair.underspecifyType
conservativeRepairOrdering = underspecificationPreferredToUnsupportedPromotion

------------------------------------------------------------------------
-- There is deliberately no constructor from mismatch evidence to ontology
-- truth.  A proposal remains reviewable evidence.
------------------------------------------------------------------------

data MismatchTruthPromotionPermission : Set where

mismatchCannotAssertReplacementTruth :
  MismatchTruthPromotionPermission → ⊥
mismatchCannotAssertReplacementTruth ()
