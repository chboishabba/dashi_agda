module DASHI.Foundations.WetteFiniteDerivabilityBernaysBridgeExact where

------------------------------------------------------------------------
-- FINITE DERIVABILITY / BERNAYS CROSS-POLLINATION
--
-- WetteBernaysConsistencyDeductionBoundaryExact deliberately left Derivable
-- abstract.  WetteFiniteDeductionTraceExact now supplies a proof-carrying
-- finite derivation object.  This module composes the two without claiming that
-- Wette's historical axiom basis, consistency formula, or contradiction formula
-- have already been recovered.
--
-- The result is an executable theorem shape:
--
--   finite proof of Con
--     + supplied Con-to-contradiction reduction
--     -> finite proof of contradiction
--     -> encoded machine reachability of contradiction.
--
-- The final promotion from a contradiction derivation to metatheoretic absurdity
-- still requires the separate ContradictionReflection owner.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Foundations.WetteConstructiveAutomatonExact as W
import DASHI.Foundations.WetteFiniteDeductionTraceExact as Trace
import DASHI.Foundations.WetteBernaysConsistencyDeductionBoundaryExact as Bernays

------------------------------------------------------------------------
-- Turn finite derivability from one designated source/axiom state into the
-- abstract Derivable family expected by the Bernays boundary.
------------------------------------------------------------------------

finiteTraceDerivabilityKernel :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (axiomState consistencySentence contradictionSentence : W.Syntax simulation) →
  (Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
   Trace.FiniteDerivationWitness simulation axiomState contradictionSentence) →
  Bernays.InternalConsistencyDeductionKernel
finiteTraceDerivabilityKernel simulation
  axiomState consistencySentence contradictionSentence reduction =
  record
    { Formula = W.Syntax simulation
    ; Derivable = Trace.FiniteDerivationWitness simulation axiomState
    ; consistencySentence = consistencySentence
    ; contradictionSentence = contradictionSentence
    ; internalConsistencyProofYieldsContradiction = reduction
    }

------------------------------------------------------------------------
-- A concrete finite trace to the consistency sentence is exactly the proof
-- datum required by InternalConsistencyProofClaim for this instantiated kernel.
------------------------------------------------------------------------

finiteConsistencyClaim :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (axiomState consistencySentence contradictionSentence : W.Syntax simulation) →
  (reduction :
    Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
    Trace.FiniteDerivationWitness simulation axiomState contradictionSentence) →
  Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
  Bernays.InternalConsistencyProofClaim
    (finiteTraceDerivabilityKernel simulation
      axiomState consistencySentence contradictionSentence reduction)
finiteConsistencyClaim simulation axiomState consistencySentence
  contradictionSentence reduction proof =
  Bernays.internalConsistencyProofClaim proof

finiteConsistencyTraceYieldsContradictionTrace :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (axiomState consistencySentence contradictionSentence : W.Syntax simulation) →
  (reduction :
    Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
    Trace.FiniteDerivationWitness simulation axiomState contradictionSentence) →
  Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
  Trace.FiniteDerivationWitness simulation axiomState contradictionSentence
finiteConsistencyTraceYieldsContradictionTrace simulation axiomState
  consistencySentence contradictionSentence reduction proof =
  Bernays.deriveInternalContradiction
    (finiteTraceDerivabilityKernel simulation
      axiomState consistencySentence contradictionSentence reduction)
    (finiteConsistencyClaim simulation axiomState consistencySentence
      contradictionSentence reduction proof)

------------------------------------------------------------------------
-- The proof-carrying contradiction trace projects into arithmetic/machine
-- reachability by the already-proved finite trace simulation theorem.
------------------------------------------------------------------------

finiteConsistencyTraceYieldsMachineContradictionReachability :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (axiomState consistencySentence contradictionSentence : W.Syntax simulation) →
  (reduction :
    Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
    Trace.FiniteDerivationWitness simulation axiomState contradictionSentence) →
  Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
  Trace.MachineReachabilityWitness machine
    (W.encode simulation axiomState)
    (W.encode simulation contradictionSentence)
finiteConsistencyTraceYieldsMachineContradictionReachability simulation
  axiomState consistencySentence contradictionSentence reduction proof =
  Trace.finiteDerivationProjectsToMachineReachability simulation
    (finiteConsistencyTraceYieldsContradictionTrace simulation axiomState
      consistencySentence contradictionSentence reduction proof)

------------------------------------------------------------------------
-- Reflection remains a distinct, stronger bridge.
------------------------------------------------------------------------

finiteConsistencyTraceIsAbsurdUnderReflection :
  {machine : W.WetteMachineSpec} →
  (simulation : W.WetteDeductionSimulation machine) →
  (axiomState consistencySentence contradictionSentence : W.Syntax simulation) →
  (reduction :
    Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
    Trace.FiniteDerivationWitness simulation axiomState contradictionSentence) →
  Bernays.ContradictionReflection
    (finiteTraceDerivabilityKernel simulation
      axiomState consistencySentence contradictionSentence reduction) →
  Trace.FiniteDerivationWitness simulation axiomState consistencySentence →
  ⊥
finiteConsistencyTraceIsAbsurdUnderReflection simulation axiomState
  consistencySentence contradictionSentence reduction reflection proof =
  Bernays.internalConsistencyProofClaimIsAbsurdUnderReflection
    (finiteTraceDerivabilityKernel simulation
      axiomState consistencySentence contradictionSentence reduction)
    reflection
    (finiteConsistencyClaim simulation axiomState consistencySentence
      contradictionSentence reduction proof)

------------------------------------------------------------------------
-- Scope boundary.
------------------------------------------------------------------------

record WetteFiniteDerivabilityBernaysBoundary : Set where
  constructor wetteFiniteDerivabilityBernaysBoundary
  field
    finiteTraceCanInstantiateDerivable : Bool
    finiteTraceCanInstantiateDerivableIsTrue :
      finiteTraceCanInstantiateDerivable ≡ true

    consistencyTracePlusReductionYieldsContradictionTrace : Bool
    consistencyTracePlusReductionYieldsContradictionTraceIsTrue :
      consistencyTracePlusReductionYieldsContradictionTrace ≡ true

    contradictionTraceProjectsToMachineReachability : Bool
    contradictionTraceProjectsToMachineReachabilityIsTrue :
      contradictionTraceProjectsToMachineReachability ≡ true

    finiteTraceInstantiationSuppliesHistoricalConsistencyProof : Bool
    finiteTraceInstantiationSuppliesHistoricalConsistencyProofIsFalse :
      finiteTraceInstantiationSuppliesHistoricalConsistencyProof ≡ false

    machineReachabilityIsAlreadyMetatheoreticContradiction : Bool
    machineReachabilityIsAlreadyMetatheoreticContradictionIsFalse :
      machineReachabilityIsAlreadyMetatheoreticContradiction ≡ false

canonicalWetteFiniteDerivabilityBernaysBoundary :
  WetteFiniteDerivabilityBernaysBoundary
canonicalWetteFiniteDerivabilityBernaysBoundary =
  wetteFiniteDerivabilityBernaysBoundary
    true refl
    true refl
    true refl
    false refl
    false refl
