module DASHI.Core.SectionedProjectionProvenanceBridgeExact where

------------------------------------------------------------------------
-- Sectioned projection / provenance-bearing quotient weld.
--
-- A section chooses one representative per coarse class.  That is sufficient
-- to reconstruct fibre-constant observables, but not arbitrary fine states.
-- Exact reopening requires an additional residual/fibre coordinate.  This
-- module makes that missing hypothesis explicit and then reuses the canonical
-- ProvenanceBearingQuotient core.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
import DASHI.Core.FibreRestrictionCore as Fibre
import DASHI.Core.ProvenanceBearingQuotient as Quotient

record SectionedProjection (Fine Coarse : Set) : Set₁ where
  constructor sectionedProjection
  field
    project : Fine → Coarse
    representative : Coarse → Fine
    section : (coarse : Coarse) → project (representative coarse) ≡ coarse

open SectionedProjection public

sectionedProjectionCore :
  ∀ {Fine Coarse : Set} →
  SectionedProjection Fine Coarse →
  Fibre.FibreRestrictionCore
sectionedProjectionCore {Fine} {Coarse} projection = record
  { Carrier = Fine
  ; Surface = Coarse
  ; Evidence = ⊤
  ; project = project projection
  ; Fibre = λ coarse → Σ Fine (λ fine → project projection fine ≡ coarse)
  ; restrictsFibre = λ _ coarse →
      Σ Fine (λ fine → project projection fine ≡ coarse)
  ; doesNotRecoverCarrier = true
  ; promotesTruth = false
  }

record ResidualReopening
    {Fine Coarse : Set}
    (projection : SectionedProjection Fine Coarse) : Set₁ where
  constructor residualReopening
  field
    Residual : Set
    residual : Fine → Residual
    reopen : Coarse → Residual → Fine
    reopenExact :
      (fine : Fine) →
      reopen (project projection fine) (residual fine) ≡ fine

open ResidualReopening public

residualReopeningGivesProvenanceBearingQuotient :
  ∀ {Fine Coarse : Set}
    {projection : SectionedProjection Fine Coarse} →
  ResidualReopening projection →
  Quotient.ProvenanceBearingQuotient (sectionedProjectionCore projection)
residualReopeningGivesProvenanceBearingQuotient reopening =
  Quotient.provenanceBearingQuotient
    (Residual reopening)
    (residual reopening)
    (reopen reopening)
    (reopenExact reopening)

FibreConstant :
  ∀ {Fine Coarse Value : Set} →
  (Fine → Coarse) → (Fine → Value) → Set
FibreConstant projectFine observable =
  ∀ x y → projectFine x ≡ projectFine y → observable x ≡ observable y

pullbackObservable :
  ∀ {Fine Coarse Value : Set} →
  (Fine → Coarse) → (Coarse → Value) → Fine → Value
pullbackObservable projectFine coarseObservable fine =
  coarseObservable (projectFine fine)

pullbackObservableIsFibreConstant :
  ∀ {Fine Coarse Value : Set}
    (projectFine : Fine → Coarse)
    (coarseObservable : Coarse → Value) →
  FibreConstant projectFine (pullbackObservable projectFine coarseObservable)
pullbackObservableIsFibreConstant projectFine coarseObservable x y equality =
  cong coarseObservable equality

representativeObservable :
  ∀ {Fine Coarse Value : Set} →
  SectionedProjection Fine Coarse →
  (Fine → Value) → Coarse → Value
representativeObservable projection observable coarse =
  observable (representative projection coarse)

fibreConstantObservableReconstructsFromSection :
  ∀ {Fine Coarse Value : Set}
    (projection : SectionedProjection Fine Coarse)
    (observable : Fine → Value) →
  FibreConstant (project projection) observable →
  (fine : Fine) →
  observable fine
    ≡ pullbackObservable
        (project projection)
        (representativeObservable projection observable)
        fine
fibreConstantObservableReconstructsFromSection projection observable constant fine =
  constant
    fine
    (representative projection (project projection fine))
    (sym (section projection (project projection fine)))

data SectionOnlyFineReconstructionPermission : Set where

sectionAloneCannotClaimFineReconstruction :
  SectionOnlyFineReconstructionPermission → ⊥
sectionAloneCannotClaimFineReconstruction ()

record SectionedProjectionBoundary : Set where
  constructor sectionedProjectionBoundary
  field
    sectionReconstructsFibreConstantObservables : Bool
    sectionReconstructsFibreConstantObservablesIsTrue :
      sectionReconstructsFibreConstantObservables ≡ true
    sectionAloneReconstructsEveryFineState : Bool
    sectionAloneReconstructsEveryFineStateIsFalse :
      sectionAloneReconstructsEveryFineState ≡ false
    residualCoordinateEnablesExactPNFReopening : Bool
    residualCoordinateEnablesExactPNFReopeningIsTrue :
      residualCoordinateEnablesExactPNFReopening ≡ true
    sectionHasNoFineReconstructionPermission :
      SectionOnlyFineReconstructionPermission → ⊥

canonicalSectionedProjectionBoundary : SectionedProjectionBoundary
canonicalSectionedProjectionBoundary =
  sectionedProjectionBoundary
    true refl
    false refl
    true refl
    sectionAloneCannotClaimFineReconstruction
