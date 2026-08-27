module DASHI.Cognition.PNF.PackedNormativeSparseAdmissionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)

open import DASHI.Cognition.PNF.DreamFlowRuntimeComplexityExact
  using (DreamWorkShape)
open import DASHI.Cognition.PNF.SparseFibredFrontier
  using (SparseFibredFrontierBoundary)

------------------------------------------------------------------------
-- A2 normative admission is an instance of the existing sparse-fibred rule:
-- perform the cheap projection-wide admission on every fibre, but expose/build
-- expensive local topology only for fibres admitted to the normative frontier.
-- Rejection says nothing about other semantic projections or retained parser
-- evidence.
------------------------------------------------------------------------

data NormativeAdmission : Set where
  rejectedNormative admittedNormative : NormativeAdmission

record PackedNormativeSparseArchitecture
    (Input Delta : Set) : Set₁ where
  field
    admission : Input → NormativeAdmission
    emptyNormativeDelta : Delta
    admittedSolve : Input → Delta
    referenceNormative : Input → Delta

    rejectedExact :
      (input : Input) →
      admission input ≡ rejectedNormative →
      referenceNormative input ≡ emptyNormativeDelta

    admittedExact :
      (input : Input) →
      admission input ≡ admittedNormative →
      admittedSolve input ≡ referenceNormative input

    sparseFrontierOwner : SparseFibredFrontierBoundary

open PackedNormativeSparseArchitecture public

------------------------------------------------------------------------
-- Piecewise semantic authority.  The runtime's cheap modal+aux mask supplies
-- the admission witness; durable token identity is still handled by the
-- separate PackedNormativeDeltaAuthorityBridgeExact materialization theorem.
------------------------------------------------------------------------

rejectedNormativeProjectionIsEmpty :
  ∀ {Input Delta : Set}
    (architecture : PackedNormativeSparseArchitecture Input Delta)
    (input : Input) →
    admission architecture input ≡ rejectedNormative →
    referenceNormative architecture input ≡ emptyNormativeDelta architecture
rejectedNormativeProjectionIsEmpty architecture input witness =
  rejectedExact architecture input witness

admittedNormativeSolveIsReference :
  ∀ {Input Delta : Set}
    (architecture : PackedNormativeSparseArchitecture Input Delta)
    (input : Input) →
    admission architecture input ≡ admittedNormative →
    admittedSolve architecture input ≡ referenceNormative architecture input
admittedNormativeSolveIsReference architecture input witness =
  admittedExact architecture input witness

------------------------------------------------------------------------
-- Structural work receipt.  This is the concrete N-wide admission / E-wide
-- expensive-work specialization of DreamFlowRuntimeComplexityExact.
------------------------------------------------------------------------

record PackedNormativeSparseWorkReceipt : Set where
  constructor packedNormativeSparseWorkReceipt
  field
    inputFibreCount : Nat
    admissionCheckCount : Nat
    admittedFibreCount : Nat
    topologyBuildCount : Nat
    emittedFactorCount : Nat

    admissionChecksEveryInput : admissionCheckCount ≡ inputFibreCount
    topologyOnlyForAdmitted : topologyBuildCount ≡ admittedFibreCount

    dreamWorkShape : DreamWorkShape

open PackedNormativeSparseWorkReceipt public

------------------------------------------------------------------------
-- Invalid interpretations are intentionally uninhabited.
------------------------------------------------------------------------

data RejectedNormativeFibreRequiresTopology : Set where

data RejectedNormativeFibreDeletesParserEvidence : Set where

data SparseAdmissionChangesSemanticAuthority : Set where

rejectedNormativeFibreNeedNotBuildTopology :
  RejectedNormativeFibreRequiresTopology → ⊥
rejectedNormativeFibreNeedNotBuildTopology ()

rejectionDoesNotDeleteParserEvidence :
  RejectedNormativeFibreDeletesParserEvidence → ⊥
rejectionDoesNotDeleteParserEvidence ()

sparseAdmissionDoesNotCreateAuthority :
  SparseAdmissionChangesSemanticAuthority → ⊥
sparseAdmissionDoesNotCreateAuthority ()
