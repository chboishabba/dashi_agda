module DASHI.Mathematics.Complexity.PNotEqualsNPDeterministicLocalGateAuditNoGoExact where

------------------------------------------------------------------------
-- DETERMINISTIC STATIC LOCAL-GATE AUDIT NO-GO
--
-- Context:
--   PNotEqualsNPConcreteCircuitSharedConstraintExact shows that a repeated-
--   fanout chain can be represented with one local equivalence obligation per
--   gate.
--
-- This owner asks whether a deterministic verifier can simply inspect fewer
-- than all of those local obligations.
--
-- Model:
--   * a chain witness is a list of Boolean node values;
--   * an audit mask has one Boolean per adjacent edge;
--   * true  = verify this local equality;
--   * false = skip this local equality.
--
-- The repeated-fanout chain's correct local semantics is just equality of
-- adjacent values: b AND b = b.
--
-- Main theorem:
--
--   if a static audit checks fewer edges than the chain contains,
--   there is a witness which the audit accepts but whose input/output bits
--   differ.
--
-- Construction:
--
--   true ... true | false ... false
--                  ^
--              one skipped edge
--
-- Every checked edge lies entirely inside a constant segment and therefore
-- passes.  The skipped edge hides the only semantic break.
--
-- This does NOT rule out adaptive, randomized, algebraic, cryptographic, PCP,
-- or other nonlocal verification.  It precisely kills deterministic static
-- sublinear checking of the ordinary local gate equations on this family.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Empty using (⊥)
open import Data.Nat.Base using (_<_; s≤s)
open import Data.Product using (Σ; _,_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

------------------------------------------------------------------------
-- Local static audit semantics.
------------------------------------------------------------------------

data AuditAccepts :
    List Bool →
    List Bool →
    Set where

  auditDone :
    ∀ {value} →
    AuditAccepts
      []
      (value ∷ [])

  auditChecked :
    ∀ {left right checks tailValues} →
    left ≡ right →
    AuditAccepts
      checks
      (right ∷ tailValues) →
    AuditAccepts
      (true ∷ checks)
      (left ∷ right ∷ tailValues)

  auditSkipped :
    ∀ {left right checks tailValues} →
    AuditAccepts
      checks
      (right ∷ tailValues) →
    AuditAccepts
      (false ∷ checks)
      (left ∷ right ∷ tailValues)

------------------------------------------------------------------------
-- Constant node segments satisfy every possible audit mask.
------------------------------------------------------------------------

constantNodes :
  List Bool →
  Bool →
  List Bool
constantNodes [] value =
  value ∷ []
constantNodes (check ∷ checks) value =
  value ∷ constantNodes checks value

constantNodesAcceptAnyAudit :
  (checks : List Bool)
  (value : Bool) →
  AuditAccepts checks (constantNodes checks value)
constantNodesAcceptAnyAudit [] value =
  auditDone
constantNodesAcceptAnyAudit (true ∷ checks) value =
  auditChecked
    refl
    (constantNodesAcceptAnyAudit checks value)
constantNodesAcceptAnyAudit (false ∷ checks) value =
  auditSkipped
    (constantNodesAcceptAnyAudit checks value)

------------------------------------------------------------------------
-- Insert exactly one skipped edge after an arbitrary audit prefix.
------------------------------------------------------------------------

maskWithSkippedEdge :
  List Bool →
  List Bool →
  List Bool
maskWithSkippedEdge [] suffix =
  false ∷ suffix
maskWithSkippedEdge (check ∷ prefix) suffix =
  check ∷ maskWithSkippedEdge prefix suffix

adversarialNodes :
  List Bool →
  List Bool →
  List Bool
adversarialNodes [] suffix =
  true ∷ constantNodes suffix false
adversarialNodes (check ∷ prefix) suffix =
  true ∷ adversarialNodes prefix suffix

adversarialAuditAccepted :
  (prefix suffix : List Bool) →
  AuditAccepts
    (maskWithSkippedEdge prefix suffix)
    (adversarialNodes prefix suffix)
adversarialAuditAccepted [] suffix =
  auditSkipped
    (constantNodesAcceptAnyAudit suffix false)
adversarialAuditAccepted (true ∷ prefix) suffix =
  auditChecked
    refl
    (adversarialAuditAccepted prefix suffix)
adversarialAuditAccepted (false ∷ prefix) suffix =
  auditSkipped
    (adversarialAuditAccepted prefix suffix)

------------------------------------------------------------------------
-- Endpoint extraction.
------------------------------------------------------------------------

firstNode :
  List Bool →
  Bool
firstNode [] =
  false
firstNode (value ∷ values) =
  value

lastNode :
  List Bool →
  Bool
lastNode [] =
  false
lastNode (value ∷ []) =
  value
lastNode (value ∷ next ∷ rest) =
  lastNode (next ∷ rest)

constantNodesLast :
  (checks : List Bool)
  (value : Bool) →
  lastNode (constantNodes checks value)
  ≡ value
constantNodesLast [] value =
  refl
constantNodesLast (check ∷ checks) value =
  constantNodesLast checks value

adversarialFirstIsTrue :
  (prefix suffix : List Bool) →
  firstNode (adversarialNodes prefix suffix)
  ≡ true
adversarialFirstIsTrue [] suffix =
  refl
adversarialFirstIsTrue (check ∷ prefix) suffix =
  refl

adversarialLastIsFalse :
  (prefix suffix : List Bool) →
  lastNode (adversarialNodes prefix suffix)
  ≡ false
adversarialLastIsFalse [] suffix =
  constantNodesLast suffix false
adversarialLastIsFalse (check ∷ prefix) suffix =
  adversarialLastIsFalse prefix suffix

trueNotFalse :
  true ≡ false → ⊥
trueNotFalse ()

adversarialEndpointsDiffer :
  (prefix suffix : List Bool) →
  firstNode (adversarialNodes prefix suffix)
  ≡ lastNode (adversarialNodes prefix suffix) →
  ⊥
adversarialEndpointsDiffer prefix suffix sameEndpoints =
  trueNotFalse
    (trans
      (sym (adversarialFirstIsTrue prefix suffix))
      (trans
        sameEndpoints
        (adversarialLastIsFalse prefix suffix)))

------------------------------------------------------------------------
-- Count checked local equations.
------------------------------------------------------------------------

auditLength :
  List Bool →
  Nat
auditLength [] =
  zero
auditLength (check ∷ checks) =
  suc (auditLength checks)

checkedCount :
  List Bool →
  Nat
checkedCount [] =
  zero
checkedCount (true ∷ checks) =
  suc (checkedCount checks)
checkedCount (false ∷ checks) =
  checkedCount checks

------------------------------------------------------------------------
-- If fewer equations are checked than exist, some skipped edge can be exposed
-- as a prefix/suffix decomposition.
------------------------------------------------------------------------

record SkippedEdgeDecomposition
    (mask : List Bool) : Set where
  constructor skipped-edge-decomposition
  field
    prefix : List Bool
    suffix : List Bool
    maskExact :
      mask ≡ maskWithSkippedEdge prefix suffix

open SkippedEdgeDecomposition public

fewerChecksGiveSkippedEdge :
  (mask : List Bool) →
  checkedCount mask < auditLength mask →
  SkippedEdgeDecomposition mask
fewerChecksGiveSkippedEdge [] ()
fewerChecksGiveSkippedEdge (false ∷ checks) fewer =
  skipped-edge-decomposition
    []
    checks
    refl
fewerChecksGiveSkippedEdge (true ∷ checks) (s≤s fewer)
    with fewerChecksGiveSkippedEdge checks fewer
... | skipped-edge-decomposition prefix suffix exact =
  skipped-edge-decomposition
    (true ∷ prefix)
    suffix
    (cong (true ∷_) exact)

------------------------------------------------------------------------
-- Main local-verification lower bound.
------------------------------------------------------------------------

record AcceptedWrongEndpointWitness
    (mask : List Bool) : Set where
  constructor accepted-wrong-endpoint-witness
  field
    values : List Bool
    accepted :
      AuditAccepts mask values
    endpointsDiffer :
      firstNode values ≡ lastNode values → ⊥

open AcceptedWrongEndpointWitness public

staticLocalAuditCheckingFewerEdgesIsUnsound :
  (mask : List Bool) →
  checkedCount mask < auditLength mask →
  AcceptedWrongEndpointWitness mask
staticLocalAuditCheckingFewerEdgesIsUnsound mask fewer
    with fewerChecksGiveSkippedEdge mask fewer
... | skipped-edge-decomposition prefix suffix exact =
  accepted-wrong-endpoint-witness
    (adversarialNodes prefix suffix)
    acceptedTransport
    (adversarialEndpointsDiffer prefix suffix)
  where
    acceptedTransport :
      AuditAccepts
        mask
        (adversarialNodes prefix suffix)
    acceptedTransport
      rewrite exact =
      adversarialAuditAccepted prefix suffix

------------------------------------------------------------------------
-- Consequence for the current self-diagonal route.
--
-- On this concrete chain family, deterministic static inspection of the
-- ordinary local gate equations has exact worst-case query complexity equal to
-- the number of gates: checking fewer leaves a one-edge cut adversary.
--
-- Any sub-|C| certification route must therefore use a stronger proof object
-- or verifier model than "pick a strict subset of local gate equations and
-- check them deterministically".
------------------------------------------------------------------------
