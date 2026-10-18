{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologyCandidatePointerObservableExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- SOURCE-EXACT CANDIDATE POINTER OBSERVABLE STRUCTURE
--
-- Carroll--Singh Eqs. (24)--(26):
--   O_CPO = O_A tensor O_B,
--   nontrivial Hermitian/traceless/unit-Frobenius factor operators,
--   minimizing || [H_int , O_CPO] ||_F.
--
-- Agda does not currently own the finite matrix/Frobenius tensor-operator
-- implementation.  Those remain explicit authorities rather than being
-- manufactured from names.
------------------------------------------------------------------------

record CPOCandidate : Set₁ where
  field
    LeftOperator RightOperator ProductOperator : Set

    leftOperator : LeftOperator
    rightOperator : RightOperator
    productOperator : ProductOperator

    ProductOperatorAuthority : Set
    productOperatorAuthority : ProductOperatorAuthority

    LeftHermitianAuthority : Set
    leftHermitianAuthority : LeftHermitianAuthority

    RightHermitianAuthority : Set
    rightHermitianAuthority : RightHermitianAuthority

    LeftTracelessAuthority : Set
    leftTracelessAuthority : LeftTracelessAuthority

    RightTracelessAuthority : Set
    rightTracelessAuthority : RightTracelessAuthority

    LeftUnitFrobeniusAuthority : Set
    leftUnitFrobeniusAuthority : LeftUnitFrobeniusAuthority

    RightUnitFrobeniusAuthority : Set
    rightUnitFrobeniusAuthority : RightUnitFrobeniusAuthority

    NontrivialProductAuthority : Set
    nontrivialProductAuthority : NontrivialProductAuthority

open CPOCandidate public

record CPOSearch : Set₁ where
  field
    CandidateIndex Score : Set
    candidate : CandidateIndex → CPOCandidate

    InteractionOperator : Set
    interactionOperator : InteractionOperator

    Commutator : CandidateIndex → Set
    commutator : (i : CandidateIndex) → Commutator i

    FrobeniusScoreAuthority : Set
    frobeniusScoreAuthority : FrobeniusScoreAuthority

    score : CandidateIndex → Score
    ScoreNoWorse : Score → Score → Set
    Admissible : CandidateIndex → Set

open CPOSearch public

record CPOReceipt (search : CPOSearch) : Set₁ where
  field
    selected : CandidateIndex search
    selectedAdmissible : Admissible search selected
    minimizes :
      ∀ other →
      Admissible search other →
      ScoreNoWorse search
        (score search selected)
        (score search other)

open CPOReceipt public

selectedCPOIsMinimal :
  ∀ {search : CPOSearch} →
  (receipt : CPOReceipt search) →
  (other : CandidateIndex search) →
  Admissible search other →
  ScoreNoWorse search
    (score search (selected receipt))
    (score search other)
selectedCPOIsMinimal receipt =
  minimizes receipt

record CPOPromotionBoundary : Set where
  field
    sourceDefinitionCreatesCPOExistence : Bool
    sourceDefinitionCreatesCPOExistenceIsFalse :
      sourceDefinitionCreatesCPOExistence ≡ false

    oneCPOReceiptCreatesUniqueness : Bool
    oneCPOReceiptCreatesUniquenessIsFalse :
      oneCPOReceiptCreatesUniqueness ≡ false

    productOperatorNameCreatesTensorMap : Bool
    productOperatorNameCreatesTensorMapIsFalse :
      productOperatorNameCreatesTensorMap ≡ false

    scoreNameCreatesFrobeniusNorm : Bool
    scoreNameCreatesFrobeniusNormIsFalse :
      scoreNameCreatesFrobeniusNorm ≡ false

    selectedCPOIsPhysicalPointerObservable : Bool
    selectedCPOIsPhysicalPointerObservableIsFalse :
      selectedCPOIsPhysicalPointerObservable ≡ false

canonicalCPOPromotionBoundary : CPOPromotionBoundary
canonicalCPOPromotionBoundary = record
  { sourceDefinitionCreatesCPOExistence = false
  ; sourceDefinitionCreatesCPOExistenceIsFalse = refl
  ; oneCPOReceiptCreatesUniqueness = false
  ; oneCPOReceiptCreatesUniquenessIsFalse = refl
  ; productOperatorNameCreatesTensorMap = false
  ; productOperatorNameCreatesTensorMapIsFalse = refl
  ; scoreNameCreatesFrobeniusNorm = false
  ; scoreNameCreatesFrobeniusNormIsFalse = refl
  ; selectedCPOIsPhysicalPointerObservable = false
  ; selectedCPOIsPhysicalPointerObservableIsFalse = refl
  }

carrollSinghCPOClaim : Sources.AttributionReceipt
carrollSinghCPOClaim =
  Sources.attribution-receipt
    Sources.externalSourceClaim
    "Sean M. Carroll; Ashmeet Singh, Phys. Rev. A 103, 022213 (2021)"
    "Eqs. (24)--(26): CPO is a nontrivial product observable with Hermitian traceless unit-Frobenius-norm factors minimizing the Frobenius norm of its commutator with the interaction Hamiltonian."

leanCPOOperatorSourceWrittenReceipt : Sources.AttributionReceipt
leanCPOOperatorSourceWrittenReceipt =
  Sources.attribution-receipt
    Sources.importedFormalTheoremSource
    "DASHI Lean: RequestProject.QuantumMereologyCandidatePointerObservable"
    "Source-written owner constructs the tensor-product operator and commutator exactly while leaving Frobenius realization and minimizer authority explicit; not kernel-certified until exact-head Lean evidence exists."

dashiCPOReconstructionReceipt : Sources.AttributionReceipt
dashiCPOReconstructionReceipt =
  Sources.attribution-receipt
    Sources.localFormalReconstruction
    "DASHI Agda"
    "Reconstructs the CPO search/minimality grammar with explicit tensor-map, Hermitian, traceless, Frobenius, existence, uniqueness and physical-promotion authority boundaries."
