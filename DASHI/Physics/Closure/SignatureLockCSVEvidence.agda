module DASHI.Physics.Closure.SignatureLockCSVEvidence where

open import Level using (Level; suc)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Agda.Builtin.Nat using (Nat)

open import DASHI.Geometry.MaskedQuadratic as MQ
open import DASHI.Geometry.Signature.Elimination as SE

-- Evidence bundle meant to be populated from CSV-derived ranking.
record SignatureRankCSVEvidence {n : Nat} : Set₁ where
  field
    rank : MQ.MaskedQuadratic n → Set
    rank⇒sig31 : ∀ {Q} → rank Q → MQ.signatureTag Q ≡ MQ.sig31

open SignatureRankCSVEvidence public

signatureLockFromRank :
  ∀ {n} {V : Set}
  (OP : SE.OrbitProfile V)
  (Ev : SignatureRankCSVEvidence {n})
  → SE.SignatureLock {n} V
signatureLockFromRank OP Ev =
  record
    { OP = OP
    ; eliminate = SignatureRankCSVEvidence.rank Ev
    }

signature31FromRank :
  ∀ {n} {V : Set}
  (Q : MQ.MaskedQuadratic n)
  (OP : SE.OrbitProfile V)
  (Ev : SignatureRankCSVEvidence {n})
  → SignatureRankCSVEvidence.rank Ev Q
  → MQ.signatureTag Q ≡ MQ.sig31
signature31FromRank Q OP Ev rk = SignatureRankCSVEvidence.rank⇒sig31 Ev rk
