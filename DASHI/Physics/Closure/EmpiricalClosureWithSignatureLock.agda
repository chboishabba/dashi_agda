module DASHI.Physics.Closure.EmpiricalClosureWithSignatureLock where

open import Level using (Level; zero; suc; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import DASHI.Physics.Closure.PhysicsClosureEmpirical as PCE
open import DASHI.Physics.WitnessSetPolicy as WSP
open import DASHI.Physics.Closure.SignatureLockCSVEvidence as SLCSV
open import DASHI.Geometry.MaskedQuadratic as MQ
open import DASHI.Geometry.SignatureElimination as SE

-- Bundle empirical seams with witness policy and signature-lock evidence.
record EmpiricalClosureWithSignatureLock {ℓ} (W : Set ℓ) {n : Nat} (V : Set)
  : Set (suc ℓ ⊔ suc zero) where
  field
    empirical : PCE.PhysicsClosureEmpirical
    policy : WSP.WitnessSetPolicy W
    orbitProfile : SE.OrbitProfile V
    signatureEvidence : SLCSV.SignatureRankCSVEvidence {n}

open EmpiricalClosureWithSignatureLock public

signatureLock :
  ∀ {ℓ} {W : Set ℓ} {n : Nat} {V : Set}
  → EmpiricalClosureWithSignatureLock W {n} V
  → SE.SignatureLock {n} V
signatureLock bundle =
  SLCSV.signatureLockFromRank
    (orbitProfile bundle)
    (signatureEvidence bundle)

signature31FromEvidence :
  ∀ {ℓ} {W : Set ℓ} {n : Nat} {V : Set}
  (Q : MQ.MaskedQuadratic n)
  (bundle : EmpiricalClosureWithSignatureLock W {n} V)
  → SLCSV.SignatureRankCSVEvidence.rank (signatureEvidence bundle) Q
  → MQ.signatureTag Q ≡ MQ.sig31
signature31FromEvidence Q bundle rk =
  SLCSV.signature31FromRank Q (orbitProfile bundle) (signatureEvidence bundle) rk
