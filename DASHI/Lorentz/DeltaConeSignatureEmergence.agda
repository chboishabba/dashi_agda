module DASHI.Lorentz.DeltaConeSignatureEmergence where

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Execution.Contract as Exec

record NatPair : Set where
  constructor _,_
  field
    positive : Nat
    negative : Nat

open NatPair public

data Signature : Set where
  lorentz : NatPair → Signature

record SignatureCarrier
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}) :
  Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    signatureOf : Set
    currentSignature : signatureOf
    spatialDimension : Nat
    isotropy : Set
    nondegenerate : Set
    mixed : Set

record LorentzEmergence
  {ℓx ℓs ℓδ ℓπ ℓe : Level}
  (C : Exec.Contract {ℓx} {ℓs} {ℓδ} {ℓπ} {ℓe}) :
  Set (lsuc (ℓx ⊔ ℓs ⊔ ℓδ ⊔ ℓπ ⊔ ℓe)) where
  field
    admissible : Exec.Contract.ExecutionAdmissible C
    carrier : SignatureCarrier C
    forcedSignature : Signature
    forcedSignature≡d1 :
      forcedSignature ≡ lorentz (SignatureCarrier.spatialDimension carrier , 1)

open LorentzEmergence public
