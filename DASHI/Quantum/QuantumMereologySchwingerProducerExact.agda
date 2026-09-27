{-# OPTIONS --safe #-}
module DASHI.Quantum.QuantumMereologySchwingerProducerExact where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Quantum.QuantumMereologyExact as QM
import DASHI.Quantum.QuantumMereologyInnerProductTPSAuthorityExact as Inner
import DASHI.Quantum.QuantumMereologyOperatorLocalityAuthorityExact as Locality
import DASHI.Quantum.QuantumMereologyCandidatePointerObservableExact as CPO
import DASHI.Quantum.QuantumMereologySchwingerObjectiveExact as Schwinger
import DASHI.Quantum.QuantumMereologySourceAtlasExact as Sources

------------------------------------------------------------------------
-- SAME-TPS CPO -> SCHWINGER PRODUCER
--
-- DASHI cross-module inference:
-- every candidate factorisation carries
--   abstract TPS semantics,
--   concrete inner-product TPS authority,
--   operator-locality authority,
--   a CPO search consuming that same interaction term,
--   a CPO minimizer,
--   and entropy-acceleration authorities.
--
-- None of these authorities is manufactured by the compiler.
------------------------------------------------------------------------

record AccelerationAuthority : Set₁ where
  field
    Score : Set
    linearEntropyAcceleration : Score
    pointerEntropyAcceleration : Score

    ReducedStateAuthority : Set
    reducedStateAuthority : ReducedStateAuthority

    LinearEntropySecondDerivativeAuthority : Set
    linearEntropySecondDerivativeAuthority :
      LinearEntropySecondDerivativeAuthority

    PointerProbabilityAuthority : Set
    pointerProbabilityAuthority :
      PointerProbabilityAuthority

    PointerEntropySecondDerivativeAuthority : Set
    pointerEntropySecondDerivativeAuthority :
      PointerEntropySecondDerivativeAuthority

open AccelerationAuthority public

record SameTPSProducer (W : QM.BareQuantumWorld) : Set₁ where
  field
    Candidate PointerInit : Set

    abstractTPS :
      Candidate → QM.TensorProductStructure W

    InnerTPSAuthority :
      Candidate → Set

    innerTPSAuthority :
      (candidate : Candidate) →
      InnerTPSAuthority candidate

    AbstractConcreteTPSWeld :
      Candidate → Set

    abstractConcreteTPSWeld :
      (candidate : Candidate) →
      AbstractConcreteTPSWeld candidate

    OperatorLocalityAuthority :
      Candidate → Set

    operatorLocalityAuthority :
      (candidate : Candidate) →
      OperatorLocalityAuthority candidate

    CPOSearch :
      Candidate → CPO.CPOSearch

    cpoSearch :
      (candidate : Candidate) →
      CPOSearch candidate

    SameInteractionAuthority :
      Candidate → Set

    sameInteractionAuthority :
      (candidate : Candidate) →
      SameInteractionAuthority candidate

    Admissible :
      Candidate → Set

    CPOReceipt :
      Candidate → Set

    cpoReceipt :
      (candidate : Candidate) →
      Admissible candidate →
      CPOReceipt candidate

    acceleration :
      Candidate → PointerInit → AccelerationAuthority

open SameTPSProducer public

------------------------------------------------------------------------
-- COMPILATION TO THE SOURCE-SHAPED SCHWINGER SEARCH
------------------------------------------------------------------------

record CompiledSchwingerProducer
    {W : QM.BareQuantumWorld}
    (producer : SameTPSProducer W) : Set₁ where
  field
    searchData :
      Schwinger.SchwingerSearchData W

    sameCandidateCarrier :
      Schwinger.Candidate searchData ≡
      Candidate producer

    samePointerCarrier :
      Schwinger.PointerInit searchData ≡
      PointerInit producer

    CPOToAccelerationSameObjectAuthority : Set
    cpoToAccelerationSameObjectAuthority :
      CPOToAccelerationSameObjectAuthority

open CompiledSchwingerProducer public

record SchwingerProducerBoundary : Set where
  field
    abstractTPSCreatesConcreteTensorReconstruction : Bool
    abstractTPSCreatesConcreteTensorReconstructionIsFalse :
      abstractTPSCreatesConcreteTensorReconstruction ≡ false

    localityCreatesCPOReceipt : Bool
    localityCreatesCPOReceiptIsFalse :
      localityCreatesCPOReceipt ≡ false

    cpoReceiptCreatesReducedState : Bool
    cpoReceiptCreatesReducedStateIsFalse :
      cpoReceiptCreatesReducedState ≡ false

    accelerationSocketCreatesEntropyDerivativeProof : Bool
    accelerationSocketCreatesEntropyDerivativeProofIsFalse :
      accelerationSocketCreatesEntropyDerivativeProof ≡ false

    compiledProducerCreatesMinimizerExistence : Bool
    compiledProducerCreatesMinimizerExistenceIsFalse :
      compiledProducerCreatesMinimizerExistence ≡ false

canonicalSchwingerProducerBoundary : SchwingerProducerBoundary
canonicalSchwingerProducerBoundary = record
  { abstractTPSCreatesConcreteTensorReconstruction = false
  ; abstractTPSCreatesConcreteTensorReconstructionIsFalse = refl
  ; localityCreatesCPOReceipt = false
  ; localityCreatesCPOReceiptIsFalse = refl
  ; cpoReceiptCreatesReducedState = false
  ; cpoReceiptCreatesReducedStateIsFalse = refl
  ; accelerationSocketCreatesEntropyDerivativeProof = false
  ; accelerationSocketCreatesEntropyDerivativeProofIsFalse = refl
  ; compiledProducerCreatesMinimizerExistence = false
  ; compiledProducerCreatesMinimizerExistenceIsFalse = refl
  }

dashiSameTPSProducerCompilerReceipt : Sources.AttributionReceipt
dashiSameTPSProducerCompilerReceipt =
  Sources.attribution-receipt
    Sources.crossModuleInference
    "DASHI"
    "Welds candidate-specific abstract TPS, concrete TPS authority, operator locality, same-interaction CPO search, CPO receipt and entropy-acceleration authority without creating any missing producer theorem."
