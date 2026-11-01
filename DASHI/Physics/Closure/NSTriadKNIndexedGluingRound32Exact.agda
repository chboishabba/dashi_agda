module DASHI.Physics.Closure.NSTriadKNIndexedGluingRound32Exact where

------------------------------------------------------------------------
-- DASHI CONTRIBUTION
--
-- Formalise the Round-31 same-object requirement as indexed gluing.
-- An external presentation is not allowed to replace the physical object:
-- it must be transported to the literal internal carrier and accompanied by
-- the equality witnessing that seam.  This is the typed form of the
-- 0 ~ 1 ~ 10 ~ 11 bookkeeping discussed in the fibre programme.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; _⊔_)
open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (sym; trans)

record IndexedGluing
    {a b : Level}
    (External : Set a)
    (Internal : Set b)
    (transport : External → Internal) : Set (a ⊔ b) where
  constructor indexed-gluing
  field
    externalBase : External
    internalBase : Internal
    glueExact : transport externalBase ≡ internalBase

open IndexedGluing public

transportedRepresentative :
  ∀ {a b} {External : Set a} {Internal : Set b}
    {transport : External → Internal} →
  IndexedGluing External Internal transport → Internal
transportedRepresentative gluing =
  transport (externalBase gluing)

transportedRepresentativeIsInternal :
  ∀ {a b} {External : Set a} {Internal : Set b}
    {transport : External → Internal}
    (gluing : IndexedGluing External Internal transport) →
  transportedRepresentative gluing ≡ internalBase gluing
transportedRepresentativeIsInternal = glueExact

record JoinedSameObject
    {a b : Level}
    (External : Set a)
    (Internal : Set b)
    (transport : External → Internal) : Set (a ⊔ b) where
  constructor joined-same-object
  field
    seam : IndexedGluing External Internal transport
    intrinsicRepresentative : Internal

open JoinedSameObject public

externalAndInternalAgreeAtSeam :
  ∀ {a b} {External : Set a} {Internal : Set b}
    {transport : External → Internal}
    (joined : JoinedSameObject External Internal transport) →
  transportedRepresentative (seam joined)
  ≡ internalBase (seam joined)
externalAndInternalAgreeAtSeam joined =
  transportedRepresentativeIsInternal (seam joined)

reverseSeam :
  ∀ {a b} {External : Set a} {Internal : Set b}
    {transport : External → Internal}
    (gluing : IndexedGluing External Internal transport) →
  internalBase gluing ≡ transportedRepresentative gluing
reverseSeam gluing = sym (glueExact gluing)

seamRoundTrip :
  ∀ {a b} {External : Set a} {Internal : Set b}
    {transport : External → Internal}
    (gluing : IndexedGluing External Internal transport) →
  transportedRepresentative gluing ≡ transportedRepresentative gluing
seamRoundTrip gluing =
  trans (glueExact gluing) (reverseSeam gluing)

indexedGluingInterfaceClosed : Bool
indexedGluingInterfaceClosed = true

indexedGluingInterfaceClosedIsTrue :
  indexedGluingInterfaceClosed ≡ true
indexedGluingInterfaceClosedIsTrue = refl
