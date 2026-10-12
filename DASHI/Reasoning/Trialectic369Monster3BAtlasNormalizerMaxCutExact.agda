module DASHI.Reasoning.Trialectic369Monster3BAtlasNormalizerMaxCutExact where

------------------------------------------------------------------------
-- MONSTER 3B NORMALIZER / HEISENBERG REALIZATION CURRENT MAX-CUT
--
-- PAID BY CERTIFIED SOURCE + EXACT FINITE EXECUTION:
-- * ATLAS direct 2.Suz / 2.Suz:2 12-dimensional GF(3) matrices are vendored
--   byte-for-byte with provenance/hash manifest;
-- * the inner 2.Suz pair determines a unique nondegenerate alternating form;
-- * the direct outer pair acts by symplectic similitudes with multipliers 2,1;
-- * the same basis normalization to repository X6 + X6* is computed;
-- * every source word has the canonical X6 compression pi_X g iota_X;
-- * depth-five search finds a concrete source word with irreducible degree-six
--   compression, cyclic rank six and an explicit swap01-breaking witness;
-- * PR #1105 identifies that compression with multiplication by beta=1-alpha
--   in its already-selected GF729 presentation by an explicit invertible Q;
-- * for the selected word `g2 g1 g2^-1 g1 g2^-1`, exact finite execution now
--   reconstructs the full 12x12 action in repository X6+X6* coordinates and
--   pays the asymmetric-Heisenberg central correction:
--       D=M^T C M-C is symmetric of rank 12,
--       q(x)=2 x^T D x,
--       q(x+y)+c(x,y)=q(x)+q(y)+c(Mx,My).
--
-- IMPORTANT NON-COLLAPSE:
-- the winning word does NOT stabilize the chosen X6 Lagrangian.  Compression is
-- still the lawful field-selector operator.  The new selected-word Heisenberg
-- lift pays one exact normalizer element, not the entire 2.Suz:2 normalizer,
-- Monster orbit/stabilizer semantics, output-translation equivariance, or any
-- physical realization.
--
-- REMAINING RECEIPTS:
-- 1. kernelize/import the concrete selected matrices/correction into Agda if
--    theorem authority rather than executable receipt is required;
-- 2. extend the central correction from the selected word to the normalizer
--    generators/full consumed source subgroup;
-- 3. close larger Monster action/orbit/stabilizer semantic recognition;
-- 4. instantiate output-translation equivariance downstream;
-- 5. physical normalizer realization remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Weld
import DASHI.Moonshine.Monster3BAtlasCompressionFieldSelectionBoundaryExact as Field
import DASHI.Moonshine.Monster3BAtlasSelectedHeisenbergLiftReceiptExact as SelectedLift
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Reasoning.Trialectic369MultiplicityNormalizerTranslationDescentExact as Descent

record Monster3BAtlasNormalizerBoundary : Set where
  constructor monster-3b-atlas-normalizer-boundary
  field
    certifiedDirectTwelveModuleLocated : Bool
    certifiedMonsterNormalizerRepresentationLocated : Bool
    sourceNormalizerQuotientActionExists : Bool
    sourceExtraspecialInterpretationPaid : Bool
    sourceTwelveModuleAbsolutelyIrreducible : Bool
    repositoryHeisenbergCarrierPaid : Bool
    sourceToRepositoryActionInterfacePaid : Bool
    centralCorrectionConditionExposed : Bool
    rawAtlasMatricesImported : Bool
    concreteAlternatingFormRuntimePaid : Bool
    concreteBasisNormalizationRuntimePaid : Bool
    outerSimilitudeMultiplierRuntimePaid : Bool
    globalNormalizerX6SubmoduleTargetRejected : Bool
    compressionFieldSelectorRoutePaid : Bool
    degreeSixCompressionCandidatePaid : Bool
    selectedGF729PresentationWeldRuntimePaid : Bool
    selectedWordFullTwelveActionRuntimePaid : Bool
    selectedWordQuadraticCentralCorrectionRuntimePaid : Bool
    selectedWordHeisenbergLiftRuntimePaid : Bool
    sameBasisIntertwinerAgdaKernelPaid : Bool
    fullNormalizerHeisenbergActionPaid : Bool
    fullMonsterActionOrbitStabilizerRecognitionPaid : Bool
    actualMonsterOutputTranslationEquivariancePaid : Bool
    physicalNormalizerRealizationPaid : Bool
    terminalNote : String
open Monster3BAtlasNormalizerBoundary public

canonicalMonster3BAtlasNormalizerBoundary : Monster3BAtlasNormalizerBoundary
canonicalMonster3BAtlasNormalizerBoundary =
  monster-3b-atlas-normalizer-boundary
    Source.canonicalBoundary.certifiedDirectTwelveModuleLocated
    Source.canonicalBoundary.certifiedAtlasNormalizerRepresentationLocated
    Source.canonicalBoundary.sourceSymplectic12ActionExists
    Source.canonicalBoundary.sourceExplainsActionOnExtraspecialQuotient
    Source.canonicalDirectTwelveModuleReceipt.absolutelyIrreducible
    true
    true
    true
    Source.canonicalBoundary.rawMatrixEntriesInRepo
    Field.canonicalCompressionFieldSelectionBoundary.innerAlternatingFormRuntimePaid
    Field.canonicalCompressionFieldSelectionBoundary.sameBasisSymplecticWeldRuntimePaid
    Field.canonicalCompressionFieldSelectionBoundary.outerSimilitudeMultiplierRuntimePaid
    true
    true
    Field.canonicalCompressionFieldSelectionBoundary.actualDegreeSixCompressionCandidateFound
    Field.canonicalCompressionFieldSelectionBoundary.selectedGF729PresentationWeldRuntimePaid
    SelectedLift.canonicalBoundary.selectedWordMatrixRuntimePaid
    SelectedLift.canonicalBoundary.selectedWordQuadraticCentralCorrectionPaid
    SelectedLift.canonicalBoundary.selectedWordHeisenbergLiftRuntimePaid
    SelectedLift.canonicalBoundary.selectedWordAgdaKernelMatrixProofPaid
    SelectedLift.canonicalBoundary.fullNormalizerHeisenbergActionPaid
    false
    false
    false
    "Source/matrix acquisition, symplectic normalization, the degree-six X6 field selector, its GF(729) weld, and one exact selected-word Heisenberg central lift are paid at executable-receipt level. Remaining work is full-normalizer lift/kernelization plus Monster orbit/stabilizer, output-equivariance and physical-realization semantics; no Lagrangian-stabilizer premise is reintroduced."
