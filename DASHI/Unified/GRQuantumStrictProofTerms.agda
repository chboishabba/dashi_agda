module DASHI.Unified.GRQuantumStrictProofTerms where

open import Agda.Builtin.Equality using (_≡_)

open import DASHI.Unified.GRQuantumProofTerms
import DASHI.Empirical.GRQuantumCorrespondenceBoundary as Empirical

------------------------------------------------------------------------
-- Strict refinements of the proposition-level terminal contract.

record Preimage {A B : Set} (map : A → B) (target : B) : Set where
  constructor preimage
  field
    witness : A
    mapsToTarget : map witness ≡ target
open Preimage public

record StrictSpinDoubleCoverProof : Set₁ where
  field
    base : SpinDoubleCoverProof
    exactSurjectivity :
      (rotation : SpinDoubleCoverProof.SO base) →
      Preimage (SpinDoubleCoverProof.rho base) rotation
    fiberProofAgreesWithSurjectivity :
      (rotation : SpinDoubleCoverProof.SO base) →
      SpinDoubleCoverProof.rho base
        (TwoElementFiber.first
          (SpinDoubleCoverProof.fiberIsTwoElement base rotation))
      ≡ rotation
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

record CliffordSurfaceCoherence
  (basic : CliffordUniversalProof)
  (strict : StrictCliffordUniversalProof) : Set₁ where
  field
    vectorCarrierAgreement :
      CliffordUniversalProof.Vector basic
      ≡ StrictCliffordUniversalProof.Vector strict
    scalarCarrierAgreement :
      CliffordUniversalProof.Scalar basic
      ≡ StrictCliffordUniversalProof.Scalar strict
    cliffordCarrierAgreement :
      CliffordUniversalProof.Clifford basic
      ≡ StrictCliffordUniversalProof.Clifford strict
    generatorAndRelationCompatibility : Set
    generatorAndRelationCompatibilityProof :
      generatorAndRelationCompatibility
open CliffordSurfaceCoherence public

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
    cliffordCoherence :
      CliffordSurfaceCoherence
        (TerminalGRQuantumProof.clifford propositionTerminal)
        strictClifford
    strictSpinCover : StrictSpinDoubleCoverProof
    spinCoverAgreement :
      StrictSpinDoubleCoverProof.base strictSpinCover
      ≡ TerminalGRQuantumProof.spinCover propositionTerminal
    sharedSubstrate : SharedSubstrateRecovery
    empiricalCorrespondence : Empirical.PhysicalGRQuantumCorrespondence
open StrictTerminalGRQuantumProof public

assembleStrictTerminalGRQuantumProof :
  (terminal : TerminalGRQuantumProof) →
  (clifford : StrictCliffordUniversalProof) →
  CliffordSurfaceCoherence
    (TerminalGRQuantumProof.clifford terminal)
    clifford →
  (spin : StrictSpinDoubleCoverProof) →
  StrictSpinDoubleCoverProof.base spin
    ≡ TerminalGRQuantumProof.spinCover terminal →
  SharedSubstrateRecovery →
  Empirical.PhysicalGRQuantumCorrespondence →
  StrictTerminalGRQuantumProof
assembleStrictTerminalGRQuantumProof
  terminal clifford coherence spin spinAgreement substrate empirical =
  record
    { propositionTerminal = terminal
    ; strictClifford = clifford
    ; cliffordCoherence = coherence
    ; strictSpinCover = spin
    ; spinCoverAgreement = spinAgreement
    ; sharedSubstrate = substrate
    ; empiricalCorrespondence = empirical
    }
