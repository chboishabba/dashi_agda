{-# OPTIONS --safe #-}
module DASHI.Cognition.PNF.SensibLawRedactionSpaceExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)

-- A deliberately bounded output projection. The private payload is
-- not a field of PublicOutput, so no API accessor exposes it.
record PrivateDraft : Set where
  constructor privateDraft
  field
    publicText : String
    privateText : String

record PublicOutput : Set where
  constructor publicOutput
  field
    visibleText : String

redactOutput : PrivateDraft → PublicOutput
redactOutput draft = publicOutput (PrivateDraft.publicText draft)

redactionPreservesPublicText : (draft : PrivateDraft) →
  PublicOutput.visibleText (redactOutput draft) ≡ PrivateDraft.publicText draft
redactionPreservesPublicText draft = refl

-- 'space' is an output formatting separator, not a proof of legal
-- deontic compliance, noninterference, or secure erasure.
record SpacedPublicOutput : Set where
  constructor spacedPublicOutput
  field
    first : PublicOutput
    separator : String
    second : PublicOutput

placeWithSpace : PublicOutput → PublicOutput → SpacedPublicOutput
placeWithSpace left right = spacedPublicOutput left " " right

spaceSeparatorPreserved : (left right : PublicOutput) →
  SpacedPublicOutput.separator (placeWithSpace left right) ≡ " "
spaceSeparatorPreserved left right = refl
