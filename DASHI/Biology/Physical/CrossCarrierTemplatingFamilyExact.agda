module DASHI.Biology.Physical.CrossCarrierTemplatingFamilyExact where

------------------------------------------------------------------------
-- Substrate-neutral templating family.
--
-- DNA sequence copying, protein-conformation propagation, epigenetic state
-- maintenance, bioelectric pattern stabilization, and morphology repair can all
-- instantiate a common persistence interface without being identified as the
-- same mechanism or promoted to agency.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Biology.DNAChemistryCarrier as DNA
import DASHI.Biology.Physical.PersistentCarrierTemplatingExact as Persistent

record TemplateSystem : Set₁ where
  field
    Carrier Substrate : Set
    template : Carrier → Substrate → Carrier × Substrate

open TemplateSystem public

sequenceTemplate : TemplateSystem
sequenceTemplate = record
  { Carrier = DNA.DNABase
  ; Substrate = DNA.DNABase
  ; template = λ source target → source , source
  }

conformationTemplateSystem : TemplateSystem
conformationTemplateSystem = record
  { Carrier = Persistent.Conformation
  ; Substrate = Persistent.Conformation
  ; template = λ source target →
      Persistent.conformationTemplate source target ,
      Persistent.conformationTemplate source target
  }

data EpigeneticState : Set where
  closed openState : EpigeneticState

epigeneticTemplate : TemplateSystem
epigeneticTemplate = record
  { Carrier = EpigeneticState
  ; Substrate = EpigeneticState
  ; template = λ source target → source , source
  }

data BioelectricPattern : Set where
  lowPattern highPattern : BioelectricPattern

bioelectricTemplate : TemplateSystem
bioelectricTemplate = record
  { Carrier = BioelectricPattern
  ; Substrate = BioelectricPattern
  ; template = λ source target → source , source
  }

data MorphologyPattern : Set where
  damagedPattern targetPattern : MorphologyPattern

morphologyRepairTemplate : TemplateSystem
morphologyRepairTemplate = record
  { Carrier = MorphologyPattern
  ; Substrate = MorphologyPattern
  ; template = λ source target → source , source
  }

------------------------------------------------------------------------
-- What is copied is explicitly typed by the carrier.
------------------------------------------------------------------------

sequenceCopiesSequence :
  proj₂ (template sequenceTemplate DNA.A DNA.T) ≡ DNA.A
sequenceCopiesSequence = refl

prionConformationTemplatesNormal :
  proj₂ (template conformationTemplateSystem Persistent.prion Persistent.normal)
    ≡ Persistent.prion
prionConformationTemplatesNormal = refl

epigeneticStateCanTemplateState :
  proj₂ (template epigeneticTemplate openState closed) ≡ openState
epigeneticStateCanTemplateState = refl

bioelectricPatternCanBeRetained :
  proj₂ (template bioelectricTemplate highPattern lowPattern) ≡ highPattern
bioelectricPatternCanBeRetained = refl

morphologicalTargetCanBeReimposed :
  proj₂ (template morphologyRepairTemplate targetPattern damagedPattern)
    ≡ targetPattern
morphologicalTargetCanBeReimposed = refl

-- These equal signatures support cross-domain theorem reuse only; source-level
-- physical mechanisms and evidential authority remain separate obligations.
