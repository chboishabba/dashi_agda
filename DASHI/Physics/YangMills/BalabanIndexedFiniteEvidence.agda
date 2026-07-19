module DASHI.Physics.YangMills.BalabanIndexedFiniteEvidence where

open import Agda.Primitive using (Level; _⊔_; lsuc)
open import Agda.Builtin.Nat using (Nat)

record FiniteInstance {b : Level} (Background : Set b) : Set b where
  constructor finiteInstance
  field
    latticeExtent : Nat
    blockLength : Nat
    rgScale : Nat
    background : Background
open FiniteInstance public

data FiniteEvidenceKind : Set where
  exactFinite rationalFinite intervalFinite floatingFinite : FiniteEvidenceKind

record FiniteCertificate
  {b c : Level}
  {Background : Set b}
  (instance : FiniteInstance Background)
  (Claim : FiniteInstance Background → Set c) : Set (lsuc (b ⊔ c)) where
  constructor finiteCertificate
  field
    kind : FiniteEvidenceKind
    witness : Claim instance
open FiniteCertificate public

certificateClaim :
  ∀ {b c} {Background : Set b}
  {instance : FiniteInstance Background}
  {Claim : FiniteInstance Background → Set c} →
  FiniteCertificate instance Claim → Claim instance
certificateClaim = witness

record UniversalCertificate
  {b c : Level}
  {Background : Set b}
  (Admissible : FiniteInstance Background → Set c)
  (Claim : FiniteInstance Background → Set c) : Set (lsuc (b ⊔ c)) where
  constructor universalCertificate
  field
    provesEveryAdmissible : ∀ instance → Admissible instance → Claim instance
open UniversalCertificate public

promoteUniversal :
  ∀ {b c} {Background : Set b}
  {Admissible Claim : FiniteInstance Background → Set c} →
  (∀ instance → Admissible instance → Claim instance) →
  UniversalCertificate Admissible Claim
promoteUniversal proof = universalCertificate proof
