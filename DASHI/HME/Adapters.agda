module DASHI.HME.Adapters where

open import Agda.Builtin.Nat using (Nat)
open import Data.List using (List)

open import DASHI.HME.Path
open import DASHI.Physics.ClosureGlue using (ClosureAxioms)
open ClosureAxioms public

------------------------------------------------------------------------
-- Legacy generic adapters retained for compatibility.
------------------------------------------------------------------------

record SLAdapter (Doc State : Set) : Set₁ where
  field
    extract : Doc → List State
    encode : State → Set

record CaseyAdapter {S : Set} (step : S → S) : Set₁ where
  field
    propose : List (Path step)
    score : Path step → Nat
    select : List Nat → Nat

record ZelphAdapter {S : Set} (step : S → S) : Set₁ where
  field
    Fact : Set
    export : Path step → List Fact

------------------------------------------------------------------------
-- Canonical downstream adapters.
--
-- These all consume the same ClosureAxioms-indexed HME path algebra, but
-- deliberately keep their semantic roles separate:
--
-- * SL supplies source-to-state/path encoding;
-- * Casey governs candidate proofs and decisions;
-- * Zelph exports facts from already-typed path proofs.
--
-- No adapter can redefine the closure carrier or manufacture an upstream
-- projection-defect/quadratic/signature/contraction theorem.
------------------------------------------------------------------------

record CanonicalSLAdapter
       (A : ClosureAxioms) : Set₁ where
  field
    Source : Set
    sourceState : Source → S A
    sourcePath : Source → Path (T A)
    sourcePathStartsAtEncodedState :
      (source : Source) →
      Path.start (sourcePath source) ≡ sourceState source

open CanonicalSLAdapter public

record CanonicalCaseyAdapter
       (A : ClosureAxioms)
       (ctx : CanonicalContext A) : Set₁ where
  field
    Proposal : Set
    Decision : Set

    proposalProof :
      Proposal →
      Proof A ctx

    decide :
      Proposal →
      Decision

open CanonicalCaseyAdapter public

record CanonicalZelphAdapter
       (A : ClosureAxioms)
       (ctx : CanonicalContext A) : Set₁ where
  field
    Fact : Set

    exportProofFacts :
      Proof A ctx →
      List Fact

open CanonicalZelphAdapter public

record CanonicalHMEInterfaceBundle
       (A : ClosureAxioms)
       (ctx : CanonicalContext A) : Set₁ where
  field
    sl : CanonicalSLAdapter A
    casey : CanonicalCaseyAdapter A ctx
    zelph : CanonicalZelphAdapter A ctx

open CanonicalHMEInterfaceBundle public
