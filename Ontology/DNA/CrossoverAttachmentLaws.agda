module Ontology.DNA.CrossoverAttachmentLaws where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Sigma using (Σ; fst; snd)
open import Data.Vec using (Vec)

open import Ontology.DNA.Supervoxel4Adic using (Base)

import Ontology.DNA.CrossoverAttachmentSurface as CAS
import Ontology.DNA.ChannelCodingSurface as CCS
------------------------------------------------------------------------
-- Minimal law surface on top of the DNA crossover attachment boundary.
-- This does not add new coding or chemistry semantics; it lifts exact
-- emit/admissibility coherence laws already owned by the local DNA
-- surfaces into one place that later brain-DNA imports can depend on.

record CrossoverAttachmentLawSurface : Set₁ where
  field
    attachment : CAS.CrossoverAttachmentSurface

    emitOutputGenericAdmissibility :
      ∀ {n} (xs : Vec Base n) →
      CCS.genericAdmissibilityFlag
        (snd (CCS.IntegratedChannelSurface.emit
          (CAS.CrossoverAttachmentSurface.channel attachment) xs))
        ≡
      CCS.genericAdmissibilityFlag xs

    emitOutputLengthExact :
      ∀ {n} (xs : Vec Base n) →
      fst (CCS.IntegratedChannelSurface.emit
        (CAS.CrossoverAttachmentSurface.channel attachment) xs)
        ≡ n

crossoverAttachmentLawSurface : CrossoverAttachmentLawSurface
crossoverAttachmentLawSurface = record
  { attachment = CAS.crossoverAttachmentSurface
  ; emitOutputGenericAdmissibility = λ xs → refl
  ; emitOutputLengthExact = λ xs → refl
  }
