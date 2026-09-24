module DASHI.Mathematics.Complexity.PNotEqualsNPChainGlobalInvariantCompressionExact where

------------------------------------------------------------------------
-- POSITIVE NONLOCAL COMPRESSION EXAMPLE
--
-- The deterministic-local-audit no-go is intentionally NOT a theorem that
-- every d-gate computation needs d checks.
--
-- For the repeated-fanout family used in the audit example, the entire circuit
-- computes the identity function:
--
--   output = input.
--
-- Once that global theorem is proved once, a concrete evaluation claim can be
-- certified by the single endpoint relation input = output.  This is exactly
-- the kind of reusable semantic authority the self-diagonal lane is looking
-- for on harder circuits.
--
-- The associated ordinary BooleanFormula expressing endpoint equality has
-- constant syntax size 9, independent of circuit depth.
--
-- Thus:
--
--   local-gate checking     -> linear in depth;
--   global semantic theorem -> constant per-use certificate.
--
-- The open P != NP problem is to obtain comparably strong reusable/global
-- structure for general polynomial SAT decision circuits without assuming the
-- desired lower bound or hiding it in a record field.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Vec.Base using (_∷_; [])
open import Relation.Binary.PropositionalEquality using (sym; trans)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitInlineExpansionExact as Inline
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteCircuitSharedConstraintExact as Shared
import DASHI.Mathematics.Complexity.PNotEqualsNPProgramDescriptionFormulaEmbeddingExact as FormulaSize
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit

------------------------------------------------------------------------
-- Constant-size endpoint-equality syntax.
------------------------------------------------------------------------

endpointEqualityFormula :
  Cook.BooleanFormula
endpointEqualityFormula =
  Shared.equivalenceFormula
    (Cook.variable zero)
    (Cook.variable (suc zero))

endpointEqualityFormulaNodeCount :
  FormulaSize.formulaNodeCount endpointEqualityFormula
  ≡ 9
endpointEqualityFormulaNodeCount =
  refl

------------------------------------------------------------------------
-- Reusable semantic authority.
------------------------------------------------------------------------

record ChainEndpointCertificate
    (inputValue outputValue : Bool) : Set where
  constructor chain-endpoint-certificate
  field
    endpointsAgree :
      inputValue ≡ outputValue

open ChainEndpointCertificate public

chainGlobalAuthority :
  (depth : Nat)
  (inputValue outputValue : Bool) →
  ChainEndpointCertificate inputValue outputValue →
  Circuit.evaluateCircuit
      (Inline.duplicatingCircuit depth)
      (inputValue ∷ [])
  ≡ outputValue
chainGlobalAuthority depth inputValue outputValue certificate =
  trans
    (Inline.duplicatingCircuitComputesInput depth inputValue)
    (endpointsAgree certificate)

------------------------------------------------------------------------
-- The per-use logical certificate is independent of depth.
------------------------------------------------------------------------

chainEndpointCertificateReflexive :
  (value : Bool) →
  ChainEndpointCertificate value value
chainEndpointCertificateReflexive value =
  chain-endpoint-certificate refl

chainGlobalAuthorityCorrectOnActualOutput :
  (depth : Nat)
  (value : Bool) →
  Circuit.evaluateCircuit
      (Inline.duplicatingCircuit depth)
      (value ∷ [])
  ≡ value
chainGlobalAuthorityCorrectOnActualOutput depth value =
  chainGlobalAuthority
    depth
    value
    value
    (chainEndpointCertificateReflexive value)

------------------------------------------------------------------------
-- Consequence.
--
-- A sub-|C| certificate is possible when one has already proved a semantic
-- theorem summarizing the entire circuit family.  Therefore the next search
-- target is not generic "compression", but a reusable global invariant or
-- algebraic identity for the self-evaluation family whose proof itself does
-- not amount to solving SAT.
------------------------------------------------------------------------
