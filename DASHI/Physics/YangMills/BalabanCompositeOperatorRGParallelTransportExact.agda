module DASHI.Physics.YangMills.BalabanCompositeOperatorRGParallelTransportExact where

------------------------------------------------------------------------
-- ROUND66: COMPOSITE-OPERATOR MIXING AS RG PARALLEL TRANSPORT
--
-- PRIMARY SOURCES / CALIBRATION
--
-- Janos Polonyi and Kornel Sailer,
-- "Renormalization of Composite Operators",
-- Physical Review D 63 (2001), 105006.
-- DOI: 10.1103/PhysRevD.63.105006.
-- arXiv:hep-th/0011083.
--
-- P. K. Mitter, "A non trivial fixed point in a three dimensional quantum
-- field theory", in Oberwolfach Report 17/2006,
-- "The Rigorous Renormalization Group".
-- DOI of report: 10.4171/OWR/2006/17.
--
-- Stefan Hollands and Christoph Kopper,
-- "The Operator Product Expansion Converges in Perturbative Field Theory",
-- Communications in Mathematical Physics 313 (2012), 257--290.
-- DOI: 10.1007/s00220-012-1457-4.
--
-- AUTHORITY BOUNDARY
--
-- Polonyi--Sailer give the RG operator-mixing/parallel-transport mechanism;
-- Hollands--Kopper give a quantitative perturbative OPE precedent.  Neither is
-- imported as a nonperturbative pure-YM local-field theorem.
--
-- DASHI CONTRIBUTION
--
-- Make the algebraic part of leaf L9 exact.  A blocked operator transforms by
-- a scale-indexed mixing map.  Iterating those maps is RG parallel transport.
-- If a distinguished operator (in particular a proposed stress tensor) is
-- protected at EVERY one-step mixing map, its complete RG transport is exactly
-- itself.  Thus the physical stress-tensor theorem is sharpened to proving the
-- one-step Ward/protection identity on the literal blocking carrier; invariance
-- under arbitrary RG depth is then no longer independent analysis.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

iterateMixing :
  ∀ {Operator : Set} →
  (Nat → Operator → Operator) → Nat → Operator → Operator
iterateMixing mix zero operator = operator
iterateMixing mix (suc depth) operator =
  mix depth (iterateMixing mix depth operator)

record CompositeRGParallelTransport (Operator : Set) : Set₁ where
  field
    oneStepMixing : Nat → Operator → Operator
    CovariantlyConstantAtStep : Nat → Operator → Set
    parallelTransportEquation : ∀ depth operator →
      CovariantlyConstantAtStep depth operator →
      oneStepMixing depth operator ≡ operator

open CompositeRGParallelTransport public

transportToDepth :
  ∀ {Operator} → CompositeRGParallelTransport Operator → Nat → Operator → Operator
transportToDepth dataSet = iterateMixing (oneStepMixing dataSet)

record ProtectedCompositeOperator
    {Operator : Set}
    (transport : CompositeRGParallelTransport Operator) : Set₁ where
  field
    protectedOperator : Operator
    protectedAtEveryStep : ∀ depth →
      oneStepMixing transport depth protectedOperator ≡ protectedOperator

open ProtectedCompositeOperator public

protectedOperatorFixedAtEveryDepth :
  ∀ {Operator}
    {transport : CompositeRGParallelTransport Operator}
    (protected : ProtectedCompositeOperator transport) →
    ∀ depth →
  transportToDepth transport depth (protectedOperator protected)
  ≡ protectedOperator protected
protectedOperatorFixedAtEveryDepth protected zero = refl
protectedOperatorFixedAtEveryDepth {transport = transport} protected (suc depth)
  rewrite protectedOperatorFixedAtEveryDepth protected depth =
  protectedAtEveryStep protected depth

record CompositeInsertionFlow
    (State Operator InsertedState : Set) : Set₁ where
  field
    stateAtScale : Nat → State
    operatorTransport : CompositeRGParallelTransport Operator
    insert : State → Operator → InsertedState
    blockedInsertedState : Nat → InsertedState → InsertedState
    insertionNaturality : ∀ depth operator →
      blockedInsertedState depth
        (insert (stateAtScale depth) operator)
      ≡ insert (stateAtScale (suc depth))
          (oneStepMixing operatorTransport depth operator)

open CompositeInsertionFlow public

protectedInsertionNaturality :
  ∀ {State Operator InsertedState}
    {flow : CompositeInsertionFlow State Operator InsertedState}
    (protected : ProtectedCompositeOperator (operatorTransport flow)) →
    ∀ depth →
  blockedInsertedState flow depth
    (insert flow (stateAtScale flow depth) (protectedOperator protected))
  ≡ insert flow (stateAtScale flow (suc depth)) (protectedOperator protected)
protectedInsertionNaturality {flow = flow} protected depth =
  trans
    (insertionNaturality flow depth (protectedOperator protected))
    (cong (insert flow (stateAtScale flow (suc depth)))
      (protectedAtEveryStep protected depth))

compositeParallelTransportAlgebraLevel : ProofLevel
compositeParallelTransportAlgebraLevel = machineChecked

protectedCompositeAllDepthTransportLevel : ProofLevel
protectedCompositeAllDepthTransportLevel = machineChecked

physicalYMCompositeMixingLevel : ProofLevel
physicalYMCompositeMixingLevel = conditional

physicalYMStressWardProtectionLevel : ProofLevel
physicalYMStressWardProtectionLevel = conditional
