module DASHI.Reasoning.Trialectic369Monster3BAtlasNormalizerMaxCutExact where

------------------------------------------------------------------------
-- MONSTER 3B NORMALIZER / HEISENBERG REALIZATION CURRENT MAX-CUT
--
-- PAID BY EXTERNAL CERTIFIED SOURCE RECEIPTS:
-- * ATLAS publishes an absolutely irreducible 12-dimensional GF(3) module for
--   2.Suz:2;
-- * Breuer--Magaard--Wilson identify the same 12-dimensional symplectic role
--   inside the Monster 3B normalizer and its extraspecial 3_+^(1+12);
-- * direct and 38-dimensional acquisition identifiers are known.
--
-- PAID IN-REPO:
-- * standard quotient carrier X6 + X6* and alternating form;
-- * exact finite Heisenberg central extension;
-- * typed source-to-repository symplectic-action interface;
-- * exact cocycle-correction condition for the asymmetric Heisenberg product;
-- * GAP acquisition helper now emits integer matrices;
-- * Python matrix consumer solves invariant alternating form, constructs a
--   standard symplectic basis, checks the central correction by polarization,
--   and searches the chosen-Lagrangian stabilizer for degree-six field
--   candidates;
-- * the direct source module's absolute irreducibility recuts the field target:
--   the FULL normalizer is not promoted to a global X6 -> X6 action.  Any
--   GF(729) selector must come from a selected element/subgroup stabilising the
--   chosen X6 Lagrangian after the 12-dimensional basis weld.
--
-- EXACT REMAINING RECEIPTS:
-- 1. acquire/import the actual published 12x12 generator entries;
-- 2. execute the installed alternating-form / basis normalization consumer;
-- 3. instantiate concrete source-to-repository generator intertwiners;
-- 4. instantiate the computed central corrections and Heisenberg lifts;
-- 5. search source words/stabilizers and test induced 6x6 minimal polynomials;
-- 6. if a degree-six irreducible candidate exists, pay the separate GF(729)
--    same-object/action recognition contract;
-- 7. instantiate output-translation equivariance downstream.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BAtlasSymplectic12SourceReceiptExact as Source
import DASHI.Moonshine.Monster3BAtlasSymplecticBasisIntertwinerCompilerExact as Weld
import DASHI.Moonshine.Monster3BAtlasLagrangianFieldSelectionBoundaryExact as Field
import DASHI.Moonshine.Monster3BFiniteHeisenbergCentralExtensionExact as H
import DASHI.Reasoning.Trialectic369MultiplicityNormalizerTranslationDescentExact as Descent

record Monster3BAtlasNormalizerBoundary : Set where
  constructor monster-3b-atlas-normalizer-boundary
  field
    certifiedDirectTwelveModuleLocated : Bool
    certifiedMonsterNormalizerRepresentationLocated : Bool
    sourceSymplecticActionExists : Bool
    sourceSp12ExtraspecialInterpretationPaid : Bool
    sourceTwelveModuleAbsolutelyIrreducible : Bool
    repositoryHeisenbergCarrierPaid : Bool
    symplecticBasisIntertwinerInterfacePaid : Bool
    centralCorrectionConditionExposed : Bool
    acquisitionScriptExportsIntegerMatrices : Bool
    matrixAnalysisConsumerInstalled : Bool
    globalNormalizerX6ActionRejected : Bool
    lagrangianStabilizerFieldSearchTyped : Bool
    rawAtlasMatricesImported : Bool
    concreteAlternatingFormComputed : Bool
    concreteSymplecticBasisChangePaid : Bool
    concreteHeisenbergCentralCorrectionPaid : Bool
    degreeSixFieldCandidatePaid : Bool
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
    true
    Field.canonicalMonster3BFieldSelectionBoundary.matrixConsumerInstalled
    Field.canonicalMonster3BFieldSelectionBoundary.globalNormalizerX6FieldActionTargetRejected
    Field.canonicalMonster3BFieldSelectionBoundary.elementOrSubgroupLagrangianStabilizerSearchRequired
    false
    false
    false
    false
    false
    false
    false
    "Source existence and the computational weld are now paid through an executable matrix consumer. The irreducible 12D source module rules out treating the whole normalizer as a preserved X6 module. Remaining external input is the actual ATLAS matrices; after import, the installed solver pays the invariant form/basis/cocycle computations and searches source elements or stabilizers for a genuine degree-six X6 field selector."
