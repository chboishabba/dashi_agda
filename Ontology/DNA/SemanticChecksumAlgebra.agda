module Ontology.DNA.SemanticChecksumAlgebra where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_)
open import Data.Empty using (⊥)
open import Data.Vec using ([]; _∷_)

open import Ontology.DNA.Supervoxel4Adic using (Base; C)
import Ontology.DNA.StreamingEncoderSurface as SES

------------------------------------------------------------------------
-- Non-trivial checksum algebra for the DNA/Brain-DNA chain.

_≢_ : {A : Set} → A → A → Set
x ≢ y = x ≡ y → ⊥

record SemanticChecksum : Set where
  constructor semanticChecksum
  field
    thermo : Nat
    hamiltonian : Nat

checksumId : SemanticChecksum
checksumId = semanticChecksum zero zero

_⊕checksum_ : SemanticChecksum → SemanticChecksum → SemanticChecksum
left ⊕checksum right =
  semanticChecksum
    (SemanticChecksum.thermo left + SemanticChecksum.thermo right)
    (SemanticChecksum.hamiltonian left + SemanticChecksum.hamiltonian right)

infixl 6 _⊕checksum_

checksumOfBases : ∀ {n} → Data.Vec.Vec Base n → SemanticChecksum
checksumOfBases xs =
  semanticChecksum
    (SES.EncoderState.thermoState (SES.stateOf xs))
    (SES.EncoderState.hamiltonianState (SES.stateOf xs))

record WholeChainChecksumLaw : Set where
  field
    sourceHop representationHop transportHop crossoverHop atomicHop :
      SemanticChecksum
    wholeChecksum : SemanticChecksum

    composedChecksum :
      wholeChecksum
      ≡
      ((((sourceHop ⊕checksum representationHop)
          ⊕checksum transportHop)
          ⊕checksum crossoverHop)
          ⊕checksum atomicHop)

    nonTrivialComposition :
      ((((sourceHop ⊕checksum representationHop)
          ⊕checksum transportHop)
          ⊕checksum crossoverHop)
          ⊕checksum atomicHop)
      ≢
      checksumId

singletonCChecksumNonTrivial :
  checksumOfBases (C ∷ []) ≢ checksumId
singletonCChecksumNonTrivial ()

singletonCWholeChainChecksumLaw : WholeChainChecksumLaw
singletonCWholeChainChecksumLaw = record
  { sourceHop = checksumId
  ; representationHop = checksumId
  ; transportHop = checksumId
  ; crossoverHop = checksumId
  ; atomicHop = checksumOfBases (C ∷ [])
  ; wholeChecksum = checksumOfBases (C ∷ [])
  ; composedChecksum = refl
  ; nonTrivialComposition = singletonCChecksumNonTrivial
  }
