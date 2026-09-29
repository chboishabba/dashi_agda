module DASHI.Law.SensibLawWrongTypePluralAdmissibilityGridExact where

------------------------------------------------------------------------
-- DASHI-original counterexample: the McNamara 3x3 grid is not sufficient
-- to recover a situated WrongType consumer's admissibility.
--
-- ATTRIBUTION / OWNERS:
--   Rob McNamara, "A System of Wrong", episode 4, user-transcribed
--   2026-09-30: the nine-cell frame-violated / logic-imposed proposal,
--   and its asserted universality; NOT established as legal fact.
--   McNamara credits Forrest Landry: independent authorship of the
--   nine-cell taxonomy remains unverified.
--   Elders Albert and Murdena Marshall with Cheryl Bartlett:
--   Etuaptmumk / Two-Eyed Seeing, provenance-respecting coordination.
--   Robin Wall Kimmerer, Braiding Sweetgrass (2013):
--   relational obligations/reciprocity; not a theorem about braids.
--   Kimberle Crenshaw (1991), DOI 10.2307/1229039:
--   intersectionality motivates attention to erased axes.
--   Luce Irigaray, This Sex Which Is Not One (English 1985):
--   critique of forced unitary representation.
--   Jacques Lacan: source-bounded interpretive grammar, NOT a legal
--   diagnostic or equivalent of Irigaray's grammar.
--   DASHI authors the finite countermodel and all proof terms.
--
-- Aboriginal/Indigenous authority is not granted by classifying an
-- Indigenous custodial obligation as 'care', 'transaction' or 'power'.
-- No universal cultural permission, legal liability, or source
-- equivalence is inferred from this fixture.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Law.SensibLawWrongTypeCareTransactionPowerGridExact as Grid
import DASHI.Culture.KimmererTwoEyedSeeingInterpretationBoundaryExact as TwoEyed
import DASHI.Culture.KimmererBraidingAcknowledgement as Kimmerer
import DASHI.Cognition.PNF.SensibLawIndigenousCustodianshipDutyCrossPollinationExact as Custody
import DASHI.Core.LacanIrigarayTernaryGrammarBridgeExact as Grammar

------------------------------------------------------------------------
-- The same nominal cell can hide a difference material to an exact
-- consumer. This is an abstract fixture, NOT a cultural case study.
------------------------------------------------------------------------

data SituatedCase : Set where
  permittedByCustodian : SituatedCase
  withheldByCustodian : SituatedCase

data CustodialDecision : Set where
  permissionEstablished : CustodialDecision
  permissionNotEstablished : CustodialDecision

gridProjection : SituatedCase → Grid.Cell
gridProjection _ = Grid.cell Grid.care Grid.transaction

permissionDecision : SituatedCase → CustodialDecision
permissionDecision permittedByCustodian = permissionEstablished
permissionDecision withheldByCustodian = permissionNotEstablished

differentDecisions :
  permissionEstablished ≡ permissionNotEstablished → ⊥
differentDecisions ()

gridErasesCustodialDecision :
  INF.NonFactorabilityWitness gridProjection permissionDecision
gridErasesCustodialDecision =
  INF.nonFactorabilityWitness
    permittedByCustodian
    withheldByCustodian
    refl
    differentDecisions

gridCannotDeterminePermission :
  INF.FactorsThrough gridProjection permissionDecision → ⊥
gridCannotDeterminePermission =
  INF.witnessRulesOutEveryFlatFactorisation
    gridErasesCustodialDecision

-- Even a richer label generated *only* from the original cell
-- cannot recover what the cell erased.
noGridOnlyRechartCanDeterminePermission :
  ∀ {Chart : Set} (rechart : Grid.Cell → Chart) →
  INF.FactorsThrough (λ s → rechart (gridProjection s))
    permissionDecision → ⊥
noGridOnlyRechartCanDeterminePermission rechart =
  INF.rechartingCannotRecoverErasedPhenomenon
    rechart gridErasesCustodialDecision

-- In contrast, a situated observer which retains both grid class and
-- the contextual permission status is adequate for this exact query.
situatedProjection : SituatedCase → Grid.Cell × CustodialDecision
situatedProjection state = gridProjection state , permissionDecision state

situatedFactorsPermission :
  INF.FactorsThrough situatedProjection permissionDecision
situatedFactorsPermission =
  INF.factorsThrough
    proj₂
    (λ _ → refl)

-- The existing source-owning modules stay distinct; they are imported
-- rather than reimplemented as ersatz Indigenous, feminist or analytic law.
-- Custodial duty, Two-Eyed Seeing, Kimmerer acknowledgement and
-- Lacan/Irigaray grammar remain separate authority/interpretation surfaces.

------------------------------------------------------------------------
-- ADMISSIBILITY IS QUERY-INDEXED, NOT A PROPERTY OF A GRID CELL.
-- A consumer may use the full situated representation if its externally
-- supplied authority/consent obligations are separately discharged.
------------------------------------------------------------------------

record AdmissibilityGate : Set₁ where
  field
    State : Set
    Observer : Set
    query : State → CustodialDecision
    observer : State → Observer
    permissionAdequate : INF.FactorsThrough observer query
    custodianAuthorityReceipt : Set
    authorityEvidence : custodianAuthorityReceipt
    sourceRevisionReceipt : Set
    sourceEvidence : sourceRevisionReceipt

-- If an alleged admissible grid-only model claims to answer this permission
-- query, its adequacy field contradicts the established collision.
record ImpossibleGridPermissionGate : Set₁ where
  field
    gridAdequacy : INF.FactorsThrough gridProjection permissionDecision
    authorityReceipt : Set
    authorityEvidence : authorityReceipt

gridPermissionGateImpossible : ImpossibleGridPermissionGate → ⊥
gridPermissionGateImpossible gate =
  gridCannotDeterminePermission
    (ImpossibleGridPermissionGate.gridAdequacy gate)

-- No such obstruction applies merely from the situated projection: it
-- factors for this query. Actual authority still needs independent evidence.
