module DASHI.Unified.GRQuantumStrictProofTerms where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Unified.GRQuantumProofTerms
import DASHI.Empirical.GRQuantumCorrespondenceBoundary as Empirical

------------------------------------------------------------------------
-- Strict refinements of the proposition-level terminal contract.
--
-- These records remove remaining opportunities to satisfy an interface with an
-- arbitrary inhabited proposition unrelated to the intended mathematical map.

record Preimage {A B : Set} (map : A → B) (target : B) : Set where
  constructor preimage
  field
    witness : A
    mapsToTarget : map witness ≡ target
open Preimage public

record StrictSpinDoubleCoverProof : Set₁ where
  field
    base : SpinDoubleCoverProof

  open SpinDoubleCoverProof base public

  field
    exactSurjectivity :
      (rotation : SO) → Preimage rho rotation

    fiberProofAgreesWithSurjectivity :
      (rotation : SO) →
      rho (TwoElementFiber.first (fiberIsTwoElement rotation)) ≡ rotation
open StrictSpinDoubleCoverProof public

record StrictCliffordUniversalProof : Set₁ where
  field
    Vector : Set
    Scalar : Set
    Q : Vector → Scalar
    Clifford : Set
    injectVector : Vector → Clifford
    multiply : Clifford → Clifford → Clifford
    scalarEmbed : Scalar → Clifford

    cliffordRelation :
      (v : Vector) →
      multiply (injectVector v) (injectVector v)
      ≡ scalarEmbed (Q v)

    TargetAlgebra : Set
    AdmissibleGeneratorMap : TargetAlgebra → Set
    FactorMap :
      (target : TargetAlgebra) →
      AdmissibleGeneratorMap target →
      Set

    factorExists :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      FactorMap target generator

    factorUnique :
      (target : TargetAlgebra) →
      (generator : AdmissibleGeneratorMap target) →
      (left right : FactorMap target generator) →
      left ≡ right
open StrictCliffordUniversalProof public

record SharedSubstrateRecovery : Set₁ where
  field
    Substrate : Set
    QuantumState : Set
    GeneralRelativisticState : Set

    quantumReadout : Substrate → QuantumState
    generalRelativisticReadout : Substrate → GeneralRelativisticState

    QuantumReference : Set
    GeneralRelativisticReference : Set

    quantumRecovery :
      (state : Substrate) →
      QuantumState → QuantumReference → Set

    generalRelativisticRecovery :
      (state : Substrate) →
      GeneralRelativisticState → GeneralRelativisticReference → Set

    quantumRecoveryProof :
      (state : Substrate) →
      (reference : QuantumReference) →
      quantumRecovery state (quantumReadout state) reference

    generalRelativisticRecoveryProof :
      (state : Substrate) →
      (reference : GeneralRelativisticReference) →
      generalRelativisticRecovery
        state
        (generalRelativisticReadout state)
        reference
open SharedSubstrateRecovery public

record StrictTerminalGRQuantumProof : Set₁ where
  field
    propositionTerminal : TerminalGRQuantumProof
    strictClifford : StrictCliffordUniversalProof
    strictSpinCover : StrictSpinDoubleCoverProof
    sharedSubstrate : SharedSubstrateRecovery
    empiricalCorrespondence : Empirical.PhysicalGRQuantumCorrespondence
open StrictTerminalGRQuantumProof public

------------------------------------------------------------------------
-- Strict terminal assembly.  No canonical inhabitant is defined.

assembleStrictTerminalGRQuantumProof :
  TerminalGRQuantumProof →
  StrictCliffordUniversalProof →
  StrictSpinDoubleCoverProof →
  SharedSubstrateRecovery →
  Empirical.PhysicalGRQuantumCorrespondence →
  StrictTerminalGRQuantumProof
assembleStrictTerminalGRQuantumProof terminal clifford spin substrate empirical =
  record
    { propositionTerminal = terminal
    ; strictClifford = clifford
    ; strictSpinCover = spin
    ; sharedSubstrate = substrate
    ; empiricalCorrespondence = empirical
    }
