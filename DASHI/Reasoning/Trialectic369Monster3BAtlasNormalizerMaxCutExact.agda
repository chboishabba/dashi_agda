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
-- * the older depth-five strict-symplectic word pays an exact selected-word
--   Heisenberg lift and the first GF(729) field-presentation weld;
-- * a depth-seven multiplier-2 primitive word pays a full-normalizer
--   center-inverting comparator;
-- * the strongest depth-eight source word
--
--       g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1
--
--   is strict symplectic, has a primitive order-728 selected-GF729 compression,
--   and carries an exact quadratic Heisenberg central correction.  Therefore
--   one source word simultaneously pays the punctured-field 728-orbit/trivial-
--   stabilizer action and a center-preserving Heisenberg lift at executable
--   exact-matrix level.
--
-- The pre-existing central-character theorem says center-preserving inertia
-- acts within a chosen zeta sector, while center inversion swaps zeta/zeta^2.
-- Hence the depth-eight word is the correct preferred target for the existing
-- phase-resolved single-zeta programme.
--
-- IMPORTANT NON-COLLAPSE:
-- none of these words stabilizes the chosen X6 Lagrangian; compression remains
-- the lawful field operator.  The finite quotient/Heisenberg realization still
-- does NOT construct the actual Monster zeta-sector state carrier or identify
-- its Fin-90 multiplicity action.  Those same-object producers are now the live
-- representation seam.
--
-- REMAINING RECEIPTS:
-- 1. construct the actual phase-resolved Monster zeta-sector action on the same
--    finite Heisenberg carrier and identify the Fin-90 multiplicity factor;
-- 2. use that to instantiate existing output-translation/multiplicity-descent
--    compilers;
-- 3. extend selected-word lifts to whatever full normalizer subgroup is actually
--    consumed downstream;
-- 4. kernelize concrete matrices/corrections when Agda theorem authority is
--    required;
-- 5. physical normalizer realization remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Weld
import DASHI.Moonshine.Monster3BAtlasCompressionFieldSelectionBoundaryExact as Field
import DASHI.Moonshine.Monster3BAtlasSelectedHeisenbergLiftReceiptExact as SelectedLift
import DASHI.Moonshine.Monster3BAtlasPrimitiveInertiaHeisenbergLiftReceiptExact as PrimitiveInertia
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
    depthFiveSelectedWordHeisenbergLiftRuntimePaid : Bool
    primitiveCenterPreservingFieldActionRuntimePaid : Bool
    primitiveCenterPreservingHeisenbergLiftRuntimePaid : Bool
    primitivePuncturedOrbit728RuntimePaid : Bool
    primitivePuncturedStabilizerTrivialRuntimePaid : Bool
    genericCentralCharacterInertiaTheoremReusable : Bool
    actualPhaseResolvedMonsterSectorActionPaid : Bool
    fin90MultiplicityActionIdentified : Bool
    sameBasisIntertwinerAgdaKernelPaid : Bool
    fullNormalizerHeisenbergActionPaid : Bool
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
    true true true
    Source.canonicalBoundary.rawMatrixEntriesInRepo
    Field.canonicalCompressionFieldSelectionBoundary.innerAlternatingFormRuntimePaid
    Field.canonicalCompressionFieldSelectionBoundary.sameBasisSymplecticWeldRuntimePaid
    Field.canonicalCompressionFieldSelectionBoundary.outerSimilitudeMultiplierRuntimePaid
    true true
    Field.canonicalCompressionFieldSelectionBoundary.actualDegreeSixCompressionCandidateFound
    Field.canonicalCompressionFieldSelectionBoundary.selectedGF729PresentationWeldRuntimePaid
    SelectedLift.canonicalBoundary.selectedWordHeisenbergLiftRuntimePaid
    PrimitiveInertia.canonicalBoundary.primitiveCompressionOrder728Paid
    PrimitiveInertia.canonicalBoundary.selectedWordHeisenbergLiftRuntimePaid
    PrimitiveInertia.canonicalBoundary.puncturedOrbit728Paid
    PrimitiveInertia.canonicalBoundary.puncturedStabilizerTrivialPaid
    PrimitiveInertia.canonicalBoundary.genericCentralCharacterInertiaTheoremReusable
    PrimitiveInertia.canonicalBoundary.actualPhaseResolvedMonsterSectorActionPaid
    PrimitiveInertia.canonicalBoundary.fin90MultiplicityActionIdentified
    PrimitiveInertia.canonicalBoundary.agdaKernelConcreteMatrixProofPaid
    SelectedLift.canonicalBoundary.fullNormalizerHeisenbergActionPaid
    false
    false
    "Field acquisition is closed: a strict-symplectic source word is explicitly primitive on the selected GF(729), has punctured orbit 728/stabilizer 1, and has a center-preserving Heisenberg lift. The live same-object seam is now the actual phase-resolved Monster zeta-sector plus Fin-90 multiplicity action; after that the existing output-translation/descent compilers become consumable. Full-normalizer/kernel/physical realization remain separate." 
