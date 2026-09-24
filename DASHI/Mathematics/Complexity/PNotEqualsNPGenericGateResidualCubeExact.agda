module DASHI.Mathematics.Complexity.PNotEqualsNPGenericGateResidualCubeExact where

------------------------------------------------------------------------
-- GENERIC FULL-CUBE THEOREM FOR LOCAL CIRCUIT RESIDUALS
--
-- For a concrete acyclic Boolean gate program, let a claimed witness assign one
-- Boolean value to every gate output.  Define the local residual at each gate:
--
--   residual_i = claimed_i XOR expected_i,
--
-- where expected_i is obtained by evaluating that gate on the input bits and
-- the previously claimed gate outputs.
--
-- Main theorem:
--
--   EVERY desired residual vector e : Bool^g is realizable by some claimed
--   gate-value witness.
--
-- Proof:
--   process gates in topological order; after recursively realizing the older
--   residuals, set
--
--     claimed_i := expected_i XOR e_i.
--
-- Then the new residual is exactly e_i.
--
-- CONSEQUENCE:
--
-- The raw local residual family of the standard shared/Tseitin circuit
-- representation is the FULL Boolean cube for every circuit, regardless of
-- uniformity, program description length, or circuit semantics.
--
-- Therefore P11 cannot be a theorem that the unconstrained local residual
-- vectors themselves lie in a low-dimensional algebraic subspace.  Any useful
-- semantic compression must first transform/restrict the proof object using
-- additional global structure.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Fin.Base using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Product using (Σ; _,_)
open import Data.Vec.Base using (Vec; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong)

import DASHI.Mathematics.Complexity.CookLevinCircuitGCTBoundary as Cook
import DASHI.Mathematics.Complexity.PNotEqualsNPConcreteBooleanCircuitDAGExact as Circuit
import DASHI.Mathematics.Complexity.PNotEqualsNPBooleanResidualFingerprintExact as Fingerprint

------------------------------------------------------------------------
-- Boolean residual algebra.
------------------------------------------------------------------------

xorBool : Bool → Bool → Bool
xorBool =
  Fingerprint.xorBool

xorExpectedResidual :
  (expected residual : Bool) →
  xorBool
    (xorBool expected residual)
    expected
  ≡ residual
xorExpectedResidual false false =
  refl
xorExpectedResidual false true =
  refl
xorExpectedResidual true false =
  refl
xorExpectedResidual true true =
  refl

------------------------------------------------------------------------
-- Residual vector for a claimed gate-value assignment.
--
-- GateProgram stores the newest gate at the outer constructor, and
-- evaluateProgram stores newest output first.  Claimed values use that same
-- newest-first ordering.
------------------------------------------------------------------------

programResiduals :
  ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates →
  Vec Bool inputs →
  Vec Bool gates →
  Vec Bool gates
programResiduals Circuit.noGates inputValues [] =
  []
programResiduals
    (Circuit.appendGate previous gate)
    inputValues
    (claimedNewest ∷ claimedPrevious) =
  xorBool
    claimedNewest
    (Circuit.evaluateGate
      gate
      inputValues
      claimedPrevious)
  ∷
  programResiduals
    previous
    inputValues
    claimedPrevious

------------------------------------------------------------------------
-- Synthesize gate claims realizing any desired residual vector.
------------------------------------------------------------------------

realizeProgramResiduals :
  ∀ {inputs gates : Nat} →
  (program : Circuit.GateProgram inputs gates) →
  Vec Bool inputs →
  Vec Bool gates →
  Vec Bool gates
realizeProgramResiduals
    Circuit.noGates
    inputValues
    [] =
  []
realizeProgramResiduals
    (Circuit.appendGate previous gate)
    inputValues
    (desiredNewest ∷ desiredPrevious) =
  claimedNewest
  ∷
  claimedPrevious
  where
    claimedPrevious : Vec Bool _
    claimedPrevious =
      realizeProgramResiduals
        previous
        inputValues
        desiredPrevious

    expectedNewest : Bool
    expectedNewest =
      Circuit.evaluateGate
        gate
        inputValues
        claimedPrevious

    claimedNewest : Bool
    claimedNewest =
      xorBool
        expectedNewest
        desiredNewest

realizeProgramResidualsExact :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (inputValues : Vec Bool inputs)
    (desired : Vec Bool gates) →
  programResiduals
    program
    inputValues
    (realizeProgramResiduals
      program
      inputValues
      desired)
  ≡ desired
realizeProgramResidualsExact
    Circuit.noGates inputValues [] =
  refl
realizeProgramResidualsExact
    (Circuit.appendGate previous gate)
    inputValues
    (desiredNewest ∷ desiredPrevious)
    rewrite
      xorExpectedResidual
        (Circuit.evaluateGate
          gate
          inputValues
          (realizeProgramResiduals
            previous
            inputValues
            desiredPrevious))
        desiredNewest
      |
      realizeProgramResidualsExact
        previous
        inputValues
        desiredPrevious =
  refl

------------------------------------------------------------------------
-- Full-cube / surjectivity theorem.
------------------------------------------------------------------------

ProgramResidualWitness :
  ∀ {inputs gates : Nat} →
  Circuit.GateProgram inputs gates →
  Vec Bool inputs →
  Vec Bool gates →
  Set
ProgramResidualWitness program inputValues desired =
  Σ (Vec Bool _) λ claimedValues →
    programResiduals
      program
      inputValues
      claimedValues
    ≡ desired

everyProgramResidualVectorIsRealizable :
  ∀ {inputs gates : Nat}
    (program : Circuit.GateProgram inputs gates)
    (inputValues : Vec Bool inputs)
    (desired : Vec Bool gates) →
  ProgramResidualWitness
    program
    inputValues
    desired
everyProgramResidualVectorIsRealizable
    program inputValues desired =
  realizeProgramResiduals
    program
    inputValues
    desired
  ,
  realizeProgramResidualsExact
    program
    inputValues
    desired

------------------------------------------------------------------------
-- Circuit-specialized statement.
------------------------------------------------------------------------

CircuitResidualWitness :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs) →
  Vec Bool inputs →
  Vec Bool (Circuit.gateCount circuit) →
  Set
CircuitResidualWitness circuit inputValues desired =
  ProgramResidualWitness
    (Circuit.program circuit)
    inputValues
    desired

everyCircuitResidualVectorIsRealizable :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs)
    (desired :
      Vec Bool (Circuit.gateCount circuit)) →
  CircuitResidualWitness
    circuit
    inputValues
    desired
everyCircuitResidualVectorIsRealizable
    circuit inputValues desired =
  everyProgramResidualVectorIsRealizable
    (Circuit.program circuit)
    inputValues
    desired

------------------------------------------------------------------------
-- All unit residuals are present for every nonempty gate program.
------------------------------------------------------------------------

unitResidual :
  ∀ {gates : Nat} →
  Fin gates →
  Vec Bool gates
unitResidual {suc gates} fzero =
  true ∷ Fingerprint.zeroWeights gates
unitResidual {suc gates} (fsuc index) =
  false ∷ unitResidual index

everyCircuitUnitResidualIsRealizable :
  ∀ {inputs : Nat}
    (circuit : Circuit.ConcreteBooleanCircuit inputs)
    (inputValues : Vec Bool inputs)
    (index : Fin (Circuit.gateCount circuit)) →
  CircuitResidualWitness
    circuit
    inputValues
    (unitResidual index)
everyCircuitUnitResidualIsRealizable
    circuit inputValues index =
  everyCircuitResidualVectorIsRealizable
    circuit
    inputValues
    (unitResidual index)

------------------------------------------------------------------------
-- Research consequence.
--
-- "Uniformity forces low-dimensional local residuals" is not merely unproved;
-- for the standard unconstrained gate-residual representation it is false in
-- the strongest possible way.  The family is all of Bool^g for each fixed
-- circuit and input.
--
-- A viable P11 theorem must therefore concern a DIFFERENT object, such as:
--
--   * a globally constrained/admissible proof code;
--   * an algebraic commitment to the full trace;
--   * a semantic invariant derived directly from the uniform program;
--   * a low-dimensional image after a transformation whose soundness is itself
--     proved and whose representation cost closes the self-size recurrence.
------------------------------------------------------------------------
