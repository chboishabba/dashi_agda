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
-- BASIS/VECTOR CORRECTION:
-- the literal VOA W_zeta carrier is a linear state carrier (it owns zero,
-- addition and scalar multiplication).  X6 x Fin90 is a finite BASIS-LABEL
-- carrier.  The previous direct whole-W_zeta <-> X6 x Fin90 target is therefore
-- retired as an overstrong/wrong-level recognition target.
--
-- The live representation seam is instead factorized as:
--   1. recognize the explicit Schrodinger 729-module as the actual H_zeta;
--   2. instantiate S_zeta = Hom_E(H_zeta,W_zeta) and the actual linear
--      evaluation/recovery H_zeta x S_zeta <-> W_zeta;
--   3. choose/recognize a genuine representation-native basis of S_zeta
--      indexed by Fin90 and identify the resulting tensor basis with the
--      finite X6 x Fin90 translation/modulation model.
--
-- The certified ninety-fold Heisenberg character isotypy strongly constrains
-- this decomposition but does NOT choose the Fin90 basis or supply the actual
-- same-object intertwiners.
--
-- REMAINING RECEIPTS:
-- 1. actual H_zeta same-object/action recognition;
-- 2. actual Hom-space evaluation/recovery on the same literal W_zeta;
-- 3. representation-native Fin90 multiplicity basis + basis action receipts;
-- 4. instantiate existing output-translation/multiplicity-descent compilers on
--    that corrected basis/linear recognition;
-- 5. extend selected-word lifts only to the normalizer subgroup actually
--    consumed downstream;
-- 6. kernelize concrete matrices/corrections when Agda theorem authority is
--    required;
-- 7. physical normalizer realization remains separate.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Weld
import DASHI.Moonshine.Monster3BAtlasCompressionFieldSelectionBoundaryExact as Field
import DASHI.Moonshine.Monster3BAtlasSelectedHeisenbergLiftReceiptExact as SelectedLift
import DASHI.Moonshine.Monster3BAtlasPrimitiveInertiaHeisenbergLiftReceiptExact as PrimitiveInertia
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as WZetaCorrection
import DASHI.Reasoning.Trialectic369Monster3BWZetaBasisVectorMaxCutExact as WZetaMaxCut
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
    wholeWZetaVectorToFiniteBasisBijectionRetired : Bool
    actualHZetaSameObjectPaid : Bool
    actualHomEvaluationSameObjectPaid : Bool
    actualFin90MultiplicityBasisPaid : Bool
    representationNativeWZetaBasisActionPaid : Bool
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
    true
    WZetaMaxCut.canonicalBoundary.actualHZetaSameObjectRecognitionPaid
    WZetaMaxCut.canonicalBoundary.actualHomEvaluationSameObjectPaid
    WZetaMaxCut.canonicalBoundary.actualMultiplicityFin90BasisPaid
    WZetaMaxCut.canonicalBoundary.representationNativeWZetaBasisActionPaid
    PrimitiveInertia.canonicalBoundary.agdaKernelConcreteMatrixProofPaid
    SelectedLift.canonicalBoundary.fullNormalizerHeisenbergActionPaid
    false
    false
    "Field/Heisenberg acquisition is closed at exact finite runtime level. The previous whole literal W_zeta vector-carrier <-> X6 x Fin90 basis-label bijection is retired. The live same-object seam is now correctly split into actual Schrodinger H_zeta recognition, actual Hom-space evaluation H_zeta x S_zeta <-> W_zeta, and a representation-native Fin90 basis/action on S_zeta. Full-normalizer/kernel/physical realization remain separate."
