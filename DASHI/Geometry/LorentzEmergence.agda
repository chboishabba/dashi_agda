module DASHI.Geometry.LorentzEmergence where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Data.Empty using (⊥)
open import Data.Product using (_×_; _,_)

open import DASHI.Execution.Contract as Exec
open import DASHI.Geometry.SignatureCombinatorics as SC

-- Proof-ready semantic seam for Lorentz emergence from the execution contract.
-- This module does not pretend the concrete semantics are already instantiated;
-- it isolates the exact obligations that must be discharged by the current
-- cone / arrow / isotropy machinery.
record EmergenceObligations
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    signature : SC.Signature
    admissible : Exec.Contract.ExecutionAdmissible C

    spatialIsotropy : Set
    isotropyConsequence : Set
    isotropyWitness : isotropyConsequence
    distinguishedArrow : Set
    arrowConsequence : Set
    arrowWitness : arrowConsequence
    coneWitness : Set
    hyperbolicNonnegativeAtWitness : Set
    hyperbolicNonnegativeWitness : hyperbolicNonnegativeAtWitness
    nondegenerate : SC.Nondegenerate signature
    mixed : SC.Mixed signature

    excludesPositiveDefinite :
      SC.q signature ≡ 0 → ⊥
    excludesNegativeDefinite :
      SC.p signature ≡ 0 → ⊥
    excludesMultipleNegative :
      (n : Nat) →
      SC.q signature ≡ suc (suc n) → ⊥

    uniqueNegative : SC.UniqueNegative signature

open EmergenceObligations public

lorentzLikeFromObligations :
  ∀ {ℓx ℓs ℓδ ℓπ ℓe}
  {C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}} →
  (O : EmergenceObligations C) →
  SC.LorentzLike (signature O)
lorentzLikeFromObligations O =
  SC.lorentzFromUniqueNegative
    (signature O)
    (uniqueNegative O)
    (nondegenerate O)

record LorentzEmergence
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe})
  : Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    obligations : EmergenceObligations C

  lorentzLike : SC.LorentzLike (signature obligations)
  lorentzLike = lorentzLikeFromObligations obligations

open LorentzEmergence public
