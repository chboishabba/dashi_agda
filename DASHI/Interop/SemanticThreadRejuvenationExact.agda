{-# OPTIONS --safe #-}
module DASHI.Interop.SemanticThreadRejuvenationExact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

-- A typed protocol model, not a claim that the Python runtime is verified.
-- A stage carries its predecessor and evidence of its transition.
record Thread : Set where
  constructor thread
  field identifier : String

record PNF (source : Thread) : Set where
  constructor pnf
  field factorCount : Nat

record World (source : Thread) (factors : PNF source) : Set where
  constructor world
  field registeredCount : Nat

record WorldRelative (source : Thread) (factors : PNF source)
                     (registered : World source factors) : Set where
  constructor relative
  field capsule : String

record Rejuvenated (source : Thread) (factors : PNF source)
                   (registered : World source factors)
                   (relativeState : WorldRelative source factors registered) : Set where
  constructor rejuvenated
  field child : Thread
        lineageRecorded : Bool
        lineageRecordedTrue : lineageRecorded ≡ true
        proofPromotionByEnrichment : Bool
        proofPromotionByEnrichmentFalse : proofPromotionByEnrichment ≡ false

lineagePreserved :
  {t : Thread} {p : PNF t} {w : World t p}
  {r : WorldRelative t p w} →
  (result : Rejuvenated t p w r) →
  Rejuvenated.lineageRecorded result ≡ true
lineagePreserved = Rejuvenated.lineageRecordedTrue

enrichmentCannotPromoteProof :
  {t : Thread} {p : PNF t} {w : World t p}
  {r : WorldRelative t p w} →
  (result : Rejuvenated t p w r) →
  Rejuvenated.proofPromotionByEnrichment result ≡ false
enrichmentCannotPromoteProof = Rejuvenated.proofPromotionByEnrichmentFalse

-- Storage authority is a protocol-level invariant.
data Database : Set where
  postgresql : Database

record CommittedWorld (source : Thread) (factors : PNF source) : Set where
  constructor committed
  field store : Database
        registered : World source factors

soleStore : {t : Thread} {p : PNF t} →
  (committedWorld : CommittedWorld t p) →
  CommittedWorld.store committedWorld ≡ postgresql
soleStore _ = refl
