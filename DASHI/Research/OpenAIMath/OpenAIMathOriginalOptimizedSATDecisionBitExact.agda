module DASHI.Research.OpenAIMath.OpenAIMathOriginalOptimizedSATDecisionBitExact where

------------------------------------------------------------------------
-- A-class positive same-original SAT decision reduction, 14 Nov 2026.
--
-- Original source: DASHI original Boolean DAG + placed Tseitin semantics,
-- imported from PR #1040 and Agda #1212.
-- Prior mathematical results: Cook--Levin/Tseitin unique extension.
-- OpenAI 378: separate fixed #SAT primitive machine and SAT output tape.
--
-- This composes EXACT ORIGINAL mathematical count equalities; it does
-- NOT claim the OAI Lean SAT.CNF Finset is the same encoded byte object,
-- or that its primitive tape/clock is already joined to this Boolean.
-- Source-written; golden Agda 2.9 kernel and transitive trust pending.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.Equality using (_≡_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Research.OpenAIMath.OpenAIMathFiniteSupportedTseitinModelsExact as Source
import DASHI.Research.OpenAIMath.OpenAIMathSharedTseitinOptimizedCNFExact as Opt
import DASHI.Research.OpenAIMath.OpenAIMathCreationOrderSerializationExact as Creation

-- The source SAT decision bit for an exact nonnegative natural count.
-- Avoid a new SAT evaluator and preserve original assignment-count semantics.
satBitOfCount : Nat → Bool
satBitOfCount zero = false
satBitOfCount (suc _) = true

-- Original unoptimized gate/CNF source, same circuit.
originalTseitinSATDecisionBitExact :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  satBitOfCount (Source.originalCompiledCNFModelCount circuit) ≡
  satBitOfCount (Source.countAcceptedCircuitInputs circuit)
originalTseitinSATDecisionBitExact circuit =
  cong satBitOfCount (Source.originalGlobalCNFCountExact circuit)

-- Original optimized 1/2/3-clause CNF, same circuit (not a fixture).
optimizedTseitinSATDecisionBitExact :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  satBitOfCount (Opt.countSourceCNF (Opt.optCircuitCNF circuit)) ≡
  satBitOfCount (Source.countAcceptedCircuitInputs circuit)
optimizedTseitinSATDecisionBitExact circuit =
  cong satBitOfCount (Opt.optGlobalCNFCountExact circuit)

-- Source circuit reverse-gate order → creation order → SAME optimized
-- original CNF model count and SAT bit. Exact JSON/Finset bytes are open.
creationOrderOptimizedSATDecisionBitExact :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  satBitOfCount
    (Opt.countSourceCNF
      (Opt.optCircuitCNF
        (Creation.decodeCircuit (Creation.encodeCircuit circuit)))) ≡
  satBitOfCount (Source.countAcceptedCircuitInputs circuit)
creationOrderOptimizedSATDecisionBitExact circuit =
  cong satBitOfCount (Creation.creationOptimizedTseitinCountExact circuit)
