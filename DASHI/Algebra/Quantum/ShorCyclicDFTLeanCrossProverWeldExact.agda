module DASHI.Algebra.Quantum.ShorCyclicDFTLeanCrossProverWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Algebra.Quantum.ShorCyclicQFTCarrierTransportExact as Source
import DASHI.Algebra.Quantum.ShorCyclicCharacterResolutionExact as Resolution

------------------------------------------------------------------------
-- CYCLIC DFT LEAN <-> AGDA SAME-OBJECT WELD FRONTIER
--
-- External source pinned by the existing DASHI source receipt:
--
--   repository : sneed-and-feed/adelic-spectral-zeta
--   revision   : 0c3e98c144796f99534f372b4aba977e6b76ee19
--   source file: formalization/MathlibUpstream/Analysis/DFT.lean
--
-- The source defines, on ZMod Q over Lean's Complex numbers,
--
--   F(i,j) = (1 / sqrt Q) * zmodChar_C(zeta)(i*j)
--
-- for a primitive Q-th root `zeta`, defines `F*` by conjugate transpose, proves
-- conjugation of the character is evaluation at the negative argument, and
-- proves both
--
--   dftMatrix * dftMatrix_star = 1
--   dftMatrix_star * dftMatrix = 1.
--
-- DASHI now owns a canonical finite Shor Vec carrier and a theorem reducing its
-- full QFT inversion to `CyclicCharacterResolutionAuthority`.  The residual is
-- therefore NOT Fourier mathematics in the abstract; it is the exact cross-
-- prover object identity between the source's ZMod/Complex DFT coordinates and
-- the Agda coefficient/Fin-Q ABI.
------------------------------------------------------------------------

sourceReceipt : Source.ShorCyclicQFTSourceReceipt
sourceReceipt = Source.canonicalShorCyclicQFTSourceReceipt

record LeanCyclicDFTSourceDetail : Set where
  constructor lean-cyclic-dft-source-detail
  field
    upstreamFile : String
    indexCarrier : String
    coefficientCarrier : String
    characterDefinition : String
    forwardDefinition : String
    inverseDefinition : String
    conjugateCharacterTheorem : String
    forwardInverseTheorem : String
    inverseForwardTheorem : String
    normalizedEntryFormula : String
open LeanCyclicDFTSourceDetail public

canonicalLeanCyclicDFTSourceDetail : LeanCyclicDFTSourceDetail
canonicalLeanCyclicDFTSourceDetail =
  lean-cyclic-dft-source-detail
    "formalization/MathlibUpstream/Analysis/DFT.lean"
    "ZMod Q"
    "Complex"
    "zmodChar_C"
    "dftMatrix"
    "dftMatrix_star"
    "char_star"
    "dft_mul_star"
    "dft_star_mul"
    "dftMatrix i j = (1 / Real.sqrt Q) * zmodChar_C zeta hzeta (i * j)"

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ExternalLeanDFTTheoremCreatesAgdaKernelProof : Set where
data MatchingDimensionsCreateIndexSameObject : Set where
data SimilarCharacterFormulaCreatesCoefficientSameObject : Set where
data SourceUnitarityCreatesShorSamplingDistribution : Set where

externalLeanDFTDoesNotCreateAgdaKernelProof :
  ExternalLeanDFTTheoremCreatesAgdaKernelProof → ⊥
externalLeanDFTDoesNotCreateAgdaKernelProof ()

matchingDimensionsDoNotCreateIndexSameObject :
  MatchingDimensionsCreateIndexSameObject → ⊥
matchingDimensionsDoNotCreateIndexSameObject ()

similarFormulaDoesNotCreateCoefficientSameObject :
  SimilarCharacterFormulaCreatesCoefficientSameObject → ⊥
similarFormulaDoesNotCreateCoefficientSameObject ()

sourceUnitarityDoesNotCreateSamplingDistribution :
  SourceUnitarityCreatesShorSamplingDistribution → ⊥
sourceUnitarityDoesNotCreateSamplingDistribution ()

------------------------------------------------------------------------
-- Exact live same-object cut.
------------------------------------------------------------------------

record CyclicDFTLeanCrossProverWeldBoundary : Set where
  constructor cyclic-dft-lean-cross-prover-weld-boundary
  field
    externalSourcePinned : Bool
    externalSourceLicencePinned : Bool
    normalizedDFTDefinitionObserved : Bool
    sourcePrimitiveRootCharacterObserved : Bool
    sourceConjugateCharacterTheoremObserved : Bool
    sourceForwardInverseTheoremObserved : Bool
    sourceInverseForwardTheoremObserved : Bool

    canonicalAgdaFinQExponentCarrierOwned : Bool
    canonicalAgdaFiniteTargetCarrierOwned : Bool
    canonicalAgdaVectorAmplitudeCarrierOwned : Bool
    agdaPowModOracleSameRegisterOwned : Bool
    agdaLiteralCharacterSumActionOwned : Bool
    agdaOneDimensionalResolutionCompilerOwned : Bool

    finQToSourceZModQSameObjectPaid : Bool
    agdaCoefficientToSourceComplexSameObjectPaid : Bool
    normalizationToInvSqrtQSameObjectPaid : Bool
    forwardPhaseToSourceCharacterSameObjectPaid : Bool
    inversePhaseToSourceConjugateCharacterSameObjectPaid : Bool

    executableCrossProverReceiptObserved : Bool
    externalLeanTheoremImportedIntoAgdaKernel : Bool
    agdaCharacterResolutionInhabited : Bool

    qftSamplingDistributionPaid : Bool
    continuedFractionSuccessProbabilityPaid : Bool
    physicalFaultTolerantRealizationPaid : Bool

    nextResidual : String
open CyclicDFTLeanCrossProverWeldBoundary public

canonicalCyclicDFTLeanCrossProverWeldBoundary :
  CyclicDFTLeanCrossProverWeldBoundary
canonicalCyclicDFTLeanCrossProverWeldBoundary =
  cyclic-dft-lean-cross-prover-weld-boundary
    true true true true true true true
    true true true true true true
    false false false false false
    false false false
    false false false
    "Pay the exact DFT same-object weld: Fin Q <-> source ZMod Q; DASHI coefficient carrier <-> Lean Complex; normalization = 1/sqrt(Q); phase(k,x) = source zmodChar_C(k*x); inversePhase(x,k) = conjugate/negative source character.  Then an executable cross-prover receipt may justify compiling the pinned Lean dft_mul_star/dft_star_mul result into the Agda CyclicCharacterResolutionAuthority.  Without that receipt, prove the same character-resolution theorem natively in Agda.  Sampling probability, continued fractions, resources and hardware remain separate."

------------------------------------------------------------------------
-- The existing source theorem and the new Agda compiler are both retained,
-- but there is deliberately no term of CyclicCharacterResolutionAuthority here.
------------------------------------------------------------------------

record CyclicDFTWeldTargetShape : Set₁ where
  constructor cyclic-dft-weld-target-shape
  field
    Coefficient : Set
    Q : Nat
    coefficientAuthority : Set
    resolutionTarget : Set
open CyclicDFTWeldTargetShape public

-- This shape names the target without manufacturing an inhabitant from source
-- provenance alone.
characterResolutionTargetShape :
  (Coefficient : Set) →
  (Q : Nat) →
  Set₁
characterResolutionTargetShape Coefficient Q =
  Σ (Set)
    (λ _ → Set)
