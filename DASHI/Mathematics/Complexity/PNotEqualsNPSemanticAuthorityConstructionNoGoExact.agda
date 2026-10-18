module DASHI.Mathematics.Complexity.PNotEqualsNPSemanticAuthorityConstructionNoGoExact where

------------------------------------------------------------------------
-- SHORT SEMANTIC AUTHORITY SIZE ALONE IS VACUOUS
--
-- A crucial P11 firewall:
--
-- If the certificate/formula constructor is allowed to know the answer of the
-- computation it is certifying, then EVERY Boolean function has a one-node
-- exact semantic authority:
--
--   authority(f,x) := constant (f x).
--
-- Its satisfiability is equivalent to f x = true.
--
-- Therefore:
--
--   "there exists a tiny formula whose SAT status equals the computation"
--
-- is not a meaningful lower-bound breakthrough by itself.
--
-- The self-diagonal route must additionally bound/construct the authority
-- WITHOUT first evaluating the target decision.  In other words, generation
-- cost and non-circular provenance are part of the theorem, not optional
-- implementation metadata.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize

------------------------------------------------------------------------
-- Omniscient one-node authority.
------------------------------------------------------------------------

omniscientAuthorityFormula :
  ∀ {Input : Set} →
  (Input → Bool) →
  Input →
  Cook.BooleanFormula
omniscientAuthorityFormula decision input =
  Cook.constant (decision input)

omniscientAuthorityHasOneNode :
  ∀ {Input : Set}
    (decision : Input → Bool)
    (input : Input) →
  FormulaSize.formulaNodeCount
    (omniscientAuthorityFormula decision input)
  ≡ 1
omniscientAuthorityHasOneNode decision input =
  refl

------------------------------------------------------------------------
-- Exact semantics.
------------------------------------------------------------------------

omniscientAuthorityComplete :
  ∀ {Input : Set}
    (decision : Input → Bool)
    (input : Input) →
  decision input ≡ true →
  Cook.Satisfiable
    (omniscientAuthorityFormula decision input)
omniscientAuthorityComplete decision input accepted
    rewrite accepted =
  Cook.satisfyingAssignment
    (λ index → false)
    refl

omniscientAuthoritySound :
  ∀ {Input : Set}
    (decision : Input → Bool)
    (input : Input) →
  Cook.Satisfiable
    (omniscientAuthorityFormula decision input) →
  decision input ≡ true
omniscientAuthoritySound decision input witness =
  Cook.evaluatesTrue witness

------------------------------------------------------------------------
-- False decisions yield literal unsatisfiability.
------------------------------------------------------------------------

omniscientAuthorityRejectingIsUnsatisfiable :
  ∀ {Input : Set}
    (decision : Input → Bool)
    (input : Input) →
  decision input ≡ false →
  Cook.Satisfiable
    (omniscientAuthorityFormula decision input) →
  ⊥
omniscientAuthorityRejectingIsUnsatisfiable
    decision input rejected witness =
  falseNotTrue
    (trans
      (sym rejected)
      (omniscientAuthoritySound
        decision input witness))
  where
    falseNotTrue : false ≡ true → ⊥
    falseNotTrue ()

------------------------------------------------------------------------
-- Research consequence.
--
-- Formula/certificate SIZE is not the right standalone invariant.  The missing
-- P11 theorem has to provide a resource-bounded constructor whose derivation of
-- the short authority does not call the very decision value being certified.
--
-- For the self-diagonal lane this means:
--
--   small authority syntax
--   + resource-bounded construction from the finite program/self-input
--   + exact soundness
--
-- must be proved together.
------------------------------------------------------------------------
