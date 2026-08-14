module DASHI.Biology.Physical.PersistentCarrierTemplatingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCE
-- Stanley B. Prusiner,
-- "Novel proteinaceous infectious particles cause scrapie",
-- Science 216 (1982), 136-144.
-- DOI: 10.1126/science.6801762.
--
-- DASHI CONTRIBUTION
-- Separate persistence/templating from agency, and make explicit that genomic
-- equality does not determine the full persistent biological carrier.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.AgenticMaterialsControlCore as Agentic

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

data Conformation : Set where
  normal prion : Conformation

normal≢prion : normal ≢ prion
normal≢prion ()

-- First argument is the template, second is the molecule being acted upon.
conformationTemplate : Conformation → Conformation → Conformation
conformationTemplate normal target = target
conformationTemplate prion target = prion

canonicalPrionPropagation : Agentic.TemplatedPropagation
canonicalPrionPropagation = record
  { Carrier = Conformation
  ; propagate = conformationTemplate
  ; selfAmplifying = true
  ; selfAmplifyingIsTrue = refl
  }

canonicalPrionBoundary : Agentic.PrionLikeBoundary canonicalPrionPropagation
canonicalPrionBoundary = record
  { observationChannelAbsent = true
  ; observationChannelAbsentIsTrue = refl
  ; targetDefectAbsent = true
  ; targetDefectAbsentIsTrue = refl
  ; correctiveFeedbackAbsent = true
  ; correctiveFeedbackAbsentIsTrue = refl
  ; agencyPromoted = false
  ; agencyPromotedIsFalse = refl
  }

prionTemplatingDoesNotPromoteAgency :
  Agentic.agencyPromoted canonicalPrionBoundary ≡ false
prionTemplatingDoesNotPromoteAgency =
  Agentic.prionLikePropagationIsNotAgency canonicalPrionBoundary

------------------------------------------------------------------------
-- General persistent/heritable carrier interface.
------------------------------------------------------------------------

record PersistentCarrier : Set₁ where
  field
    Carrier Perturbation Readout : Set
    copy : Carrier → Carrier
    perturb : Perturbation → Carrier → Carrier
    read : Carrier → Readout
    repair : Carrier → Carrier

open PersistentCarrier public

record PersistentCarrierLaws (C : PersistentCarrier) : Set₁ where
  field
    copyStable : (x : Carrier C) → copy C (copy C x) ≡ copy C x
    repairStable : (x : Carrier C) → repair C (repair C x) ≡ repair C x

open PersistentCarrierLaws public

------------------------------------------------------------------------
-- Same genome, different persistent conformational state, different future.
------------------------------------------------------------------------

record BiologicalCarrierState : Set where
  constructor biologicalCarrierState
  field
    genome : Bool
    conformation : Conformation

open BiologicalCarrierState public

contactPrion : BiologicalCarrierState → BiologicalCarrierState
contactPrion (biologicalCarrierState g c) =
  biologicalCarrierState g (conformationTemplate prion c)

sameGenomeNormal sameGenomePrion : BiologicalCarrierState
sameGenomeNormal = biologicalCarrierState false normal
sameGenomePrion = biologicalCarrierState false prion

sameGenomeProjection :
  genome sameGenomeNormal ≡ genome sameGenomePrion
sameGenomeProjection = refl

finePersistentStatesDiffer :
  sameGenomeNormal ≢ sameGenomePrion
finePersistentStatesDiffer eq = normal≢prion (cong conformation eq)

sameGenomeDoesNotReconstructPersistentCarrier :
  Σ BiologicalCarrierState (λ left →
    Σ BiologicalCarrierState (λ right →
      genome left ≡ genome right × left ≢ right))
sameGenomeDoesNotReconstructPersistentCarrier =
  sameGenomeNormal , (sameGenomePrion , (refl , finePersistentStatesDiffer))

prionContactPreservesGenome :
  (x : BiologicalCarrierState) → genome (contactPrion x) ≡ genome x
prionContactPreservesGenome (biologicalCarrierState g c) = refl

prionContactConvertsNormal :
  conformation (contactPrion sameGenomeNormal) ≡ prion
prionContactConvertsNormal = refl
