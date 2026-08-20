module DASHI.Core.CompositionalComplianceExact where

------------------------------------------------------------------------
-- COMPOSITIONAL COMPLIANCE / PROOF-CARRYING STATE
--
-- A receipt is treated as evidence for a predicate over an artifact and its
-- parents, not as a bag of hashes.  Composition preserves the intermediate
-- witness explicitly, which is the non-cryptographic theorem shape underlying
-- the proof-carrying-data analogy used by SeaMeInIt and the reopenable-state
-- discipline used across DASHI.
--
-- References:
--
-- George C. Necula, "Compiling with Proofs", PhD thesis, Carnegie Mellon
-- University, 1998, Technical Report CMU-CS-98-154.  No DOI recorded here.
--
-- Nir Bitansky, Ran Canetti, Alessandro Chiesa, Eran Tromer,
-- "Recursive composition and bootstrapping for SNARKS and proof-carrying
-- data", STOC 2013, pp. 111-120.
-- DOI: 10.1145/2488608.2488623.
--
-- These references motivate proof-carrying policy/compliance composition.  The
-- exact dependent records below are ordinary Agda propositions; no SNARK or
-- cryptographic soundness claim is made.
------------------------------------------------------------------------

open import Agda.Builtin.String using (String)
open import Data.Product using (Σ; _,_)

------------------------------------------------------------------------
-- One certified transformation.
------------------------------------------------------------------------

record CertifiedStage
    (Input Output : Set)
    (Complies : Input → Output → Set) : Set₁ where
  constructor certifiedStage
  field
    input : Input
    output : Output
    compliance : Complies input output
    policyReference : String
    producerReference : String

open CertifiedStage public

------------------------------------------------------------------------
-- Sequential compliance is not flattened: the intermediate artifact is part
-- of the proposition.  This blocks splicing proofs that refer to unrelated
-- carriers merely because their endpoint types happen to match.
------------------------------------------------------------------------

CompositeCompliance :
  ∀ {A B C : Set} →
  (A → B → Set) → (B → C → Set) → A → C → Set
CompositeCompliance first second a c =
  Σ _ (λ b → first a b × second b c)
  where
    open import Data.Product using (_×_)

composeCertifiedStages :
  ∀ {A B C}
    {First : A → B → Set}
    {Second : B → C → Set}
    (left : CertifiedStage A B First)
    (right : CertifiedStage B C Second) →
  input right ≡ output left →
  CompositeCompliance First Second (input left) (output right)
composeCertifiedStages left right same with same
... | refl = output left , (compliance left , compliance right)

------------------------------------------------------------------------
-- A downstream stage may explicitly require an upstream compliance witness.
-- This is the typed shape of a gate such as
--
--   authorised body -> ROM -> seam -> panel -> manufacturing.
------------------------------------------------------------------------

record DependentCertifiedStage
    (Input Output : Set)
    (UpstreamValid : Input → Set)
    (Complies : Input → Output → Set) : Set₁ where
  constructor dependentCertifiedStage
  field
    input : Input
    upstreamValidity : UpstreamValid input
    output : Output
    compliance : Complies input output

open DependentCertifiedStage public

------------------------------------------------------------------------
-- Boundary: a proof that a numerical/property predicate holds is not itself a
-- governance/authority witness unless the declared downstream predicate asks
-- for that authority explicitly.
------------------------------------------------------------------------
