module DASHI.Reasoning.Trialectic369Monster3BWZetaBasisVectorMaxCutExact where

------------------------------------------------------------------------
-- MONSTER 3B W_zeta: CORRECTED BASIS/VECTOR SAME-OBJECT MAX-CUT
--
-- The finite 729 x 90 model is a BASIS-LABEL model.  The literal Moonshine-VOA
-- zeta eigenspace is a state/vector carrier.  Therefore the remaining Monster
-- recognition must not be stated as a bijection between every literal vector
-- and the 65,610 finite basis labels.
--
-- The live cut is representation-native on BOTH factors:
--
--   H_zeta : explicit 729-dimensional finite-Heisenberg Schrodinger module;
--   S_zeta : Hom_E(H_zeta,W_zeta), with source-native 6.Suz multiplicity
--            structure and candidate degree split 12 + 78 = 90.
--
-- Existing owners pay:
--
--   * selected literal 3B / certified central-zeta kernel same-element data;
--   * explicit Schrodinger carrier and full finite-Heisenberg action;
--   * constructive 3^6 search and unconditional Schrodinger irreducibility;
--   * fixed-phase nonlinear CHARACTER-SIGNATURE uniqueness;
--   * a source-written companion-Lean theorem that equal characters determine
--     simple finite-group representations without algebraic closure;
--   * the canonical linear multiplicity target S_zeta = Hom_E(H_zeta,W_zeta);
--   * Barraclough--Wilson's source-native extension/tensor/induction route for
--     a 6.Suz multiplicity representation, with candidate families 12a/b and
--     78a/b and pair-level Monster-occurrence matchers already written.
--
-- Proof-relevance correction:
--
-- Several historical recognition records used fields of type `Set` to name
-- outstanding obligations.  Such fields store proposition TYPES, not proofs
-- inhabiting those propositions.  The new hardening owner wraps those records
-- with explicit inhabitants.  Consequently no terminal same-object promotion
-- may count a typed obligation as paid recognition.
--
-- What remains is correspondingly narrow:
--
--   (1) construct the proof-relevant SAME W_zeta|E irreducible constituent
--       attachment, then transport one selected constituent and the explicit
--       Schrodinger action through the finite-character theorem;
--   (2) execute the existing GAP/CTblLib candidate + main/quotient matchers,
--       then orient the individual zeta member of the 12a/b and 78a/b pairs;
--   (3) instantiate H_zeta x S_zeta -> W_zeta evaluation/recovery on the SAME
--       literal W_zeta vector carrier with an inhabited linear intertwiner;
--   (4) only for coordinate consumers, choose a genuine basis of S_zeta and
--       identify it with Fin 90, then prove tensor-basis translation/modulation
--       compatibility with proof-relevant witnesses.
--
-- Thus Fin 90 is no longer the primary multiplicity object: it is a possible
-- basis coordinate on the actual 6.Suz-structured Hom-space representation.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as Kernel
import DASHI.Moonshine.Monster3BBarracloughWilson729SourceReceiptExact as BW
import DASHI.Moonshine.Monster3BWZetaBasisVectorRecognitionCorrectionExact as Correction
import DASHI.Moonshine.Monster3BFiniteProjectorModelExact as Model
import DASHI.Moonshine.Monster3BFiniteSchrodingerHilbertLiftExact as Schrodinger
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Irreducibility
import DASHI.Moonshine.Monster3BFiniteCharacterDeterminationLeanReceiptExact as CharacterLean
import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as Hardening
import DASHI.Reasoning.Trialectic369SchrodingerHZetaRecognitionMaxCutExact as HZeta
import DASHI.Wikimedia.IbrahimMonster3BLinearMultiplicityHomSpaceExact as Hom
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMultiplicityCharacterSnowballExact as Suzuki
import DASHI.Wikimedia.IbrahimMonster3BSuzukiMainQuotientSameObjectSnowballExact as SuzukiSame

------------------------------------------------------------------------
-- 1. Corrected source package.  This still names the historical objects; the
--    paid wrapper below is the terminal promotion gate.
------------------------------------------------------------------------

record CorrectedWZetaRecognitionSource (Monster K : Set) : Setω where
  field
    kernelAttachment : Kernel.Actual3BKernelSameElementAttachment Monster K

    schrodingerIsActualHZeta : HZeta.SchrodingerIsActualHZeta

    multiplicityHomSpace : Hom.ActualLinearMultiplicityHomSpace

    literalWZetaIsHomChosenCarrier :
      Hom.ChosenZetaCarrier multiplicityHomSpace
      ≡ Kernel.selectedLiteralZetaSector kernelAttachment

    multiplicityBasis :
      Correction.ActualMultiplicityBasisRecognition multiplicityHomSpace

    basisRecognition :
      Correction.ActualZetaBasisRecognition
        (Kernel.selectedLiteralZetaSector kernelAttachment)

    basisVectorCompatibility :
      Correction.WZetaBasisVectorRecognition
        (Kernel.selectedLiteralZetaSector kernelAttachment)
        multiplicityHomSpace

open CorrectedWZetaRecognitionSource public

------------------------------------------------------------------------
-- 1a. Proof-relevant terminal wrapper.
--
-- This is intentionally stronger than merely inhabiting the historical source
-- record: every Set-valued promotion obligation needed downstream must itself
-- have an inhabitant.
------------------------------------------------------------------------

record PaidCorrectedWZetaRecognitionSource
    (Monster K : Set)
    (source : CorrectedWZetaRecognitionSource Monster K) : Setω where
  field
    paidHZetaRecognition :
      Hardening.PaidSchrodingerIsActualHZeta
        (schrodingerIsActualHZeta source)

    paidHomEvaluation :
      Hardening.PaidActualLinearMultiplicityHomSpace
        (multiplicityHomSpace source)

    paidMultiplicityBasis :
      Hardening.PaidActualMultiplicityBasisRecognition
        (multiplicityBasis source)

    paidZetaBasis :
      Hardening.PaidActualZetaBasisRecognition
        (basisRecognition source)

    paidBasisVectorCompatibility :
      Hardening.PaidWZetaBasisVectorRecognition
        (basisVectorCompatibility source)

open PaidCorrectedWZetaRecognitionSource public

------------------------------------------------------------------------
-- 2. Paid donors are exposed without promoting them to the missing source.
------------------------------------------------------------------------

barracloughWilsonBoundary : BW.Boundary
barracloughWilsonBoundary = BW.canonicalBoundary

schrodingerBoundary : Schrodinger.SchrodingerHilbertLiftBoundary
schrodingerBoundary = Schrodinger.canonicalSchrodingerHilbertLiftBoundary

irreducibilityBoundary : Irreducibility.Boundary
irreducibilityBoundary = Irreducibility.canonicalBoundary

characterLeanBoundary : CharacterLean.Boundary
characterLeanBoundary = CharacterLean.canonicalBoundary

hardeningBoundary : Hardening.Boundary
hardeningBoundary = Hardening.canonicalBoundary

linearHomFrontier : Hom.LinearMultiplicityHomFrontier
linearHomFrontier = Hom.currentLinearMultiplicityHomFrontier

suzukiMultiplicityFrontier : Suzuki.SuzukiMultiplicityFrontier
suzukiMultiplicityFrontier = Suzuki.currentSuzukiMultiplicityFrontier

suzukiSameObjectFrontier : SuzukiSame.SuzukiMainSameObjectFrontier
suzukiSameObjectFrontier = SuzukiSame.currentSuzukiMainSameObjectFrontier

------------------------------------------------------------------------
-- 3. Attribution / WrongType firewalls for the recut.
------------------------------------------------------------------------

data NinetyIsotypyCreatesMultiplicityBasis : Set where
data Degree729CreatesActualHZetaSameObject : Set where
data IrreducibilityCreatesActualHZetaSameObject : Set where
data TypedObligationCreatesPaidRecognition : Set where
data TwelvePlusSeventyEightCreatesMonsterOccurrence : Set where
data SuzukiCharacterPairCreatesIndividualZetaOrientation : Set where
data FiniteModelBasisCreatesLinearEvaluation : Set where
data HomDimensionCreatesNormalizerAction : Set where

ninetyIsotypyDoesNotCreateMultiplicityBasis :
  NinetyIsotypyCreatesMultiplicityBasis → ⊥
ninetyIsotypyDoesNotCreateMultiplicityBasis ()

degree729DoesNotCreateActualHZetaSameObject :
  Degree729CreatesActualHZetaSameObject → ⊥
degree729DoesNotCreateActualHZetaSameObject ()

irreducibilityDoesNotCreateActualHZetaSameObject :
  IrreducibilityCreatesActualHZetaSameObject → ⊥
irreducibilityDoesNotCreateActualHZetaSameObject ()

typedObligationDoesNotCreatePaidRecognition :
  TypedObligationCreatesPaidRecognition → ⊥
typedObligationDoesNotCreatePaidRecognition ()

twelvePlusSeventyEightDoesNotCreateMonsterOccurrence :
  TwelvePlusSeventyEightCreatesMonsterOccurrence → ⊥
twelvePlusSeventyEightDoesNotCreateMonsterOccurrence ()

suzukiPairDoesNotCreateIndividualZetaOrientation :
  SuzukiCharacterPairCreatesIndividualZetaOrientation → ⊥
suzukiPairDoesNotCreateIndividualZetaOrientation ()

finiteModelDoesNotCreateLinearEvaluation :
  FiniteModelBasisCreatesLinearEvaluation → ⊥
finiteModelDoesNotCreateLinearEvaluation ()

homDimensionDoesNotCreateNormalizerAction :
  HomDimensionCreatesNormalizerAction → ⊥
homDimensionDoesNotCreateNormalizerAction ()

------------------------------------------------------------------------
-- 4. Machine-readable current max-cut.
------------------------------------------------------------------------

nextResidual : String
nextResidual =
  "Schrodinger irreducibility is closed and generic equal-character simple-representation isomorphism is source-written in companion Lean. The live mathematical input is now proof-relevant same-object data, not another theorem name: construct the SAME W_zeta|E irreducible constituent decomposition with selected phase and per-constituent character witnesses; package one actual constituent and the explicit Schrodinger module in the common representation layer; then obtain the H_zeta equivariant isomorphism. On multiplicity, execute the existing CTblLib 6.Suz candidate and Suzuki-main-quotient matchers, orient the individual zeta members, instantiate S_zeta = Hom_E(H_zeta,W_zeta) with an inhabited linear evaluation intertwiner, and only then choose a proof-relevant Fin90 basis if a coordinate consumer requires it. A Set-valued obligation type is not a paid witness."

record CorrectedWZetaMaxCutBoundary : Set where
  constructor corrected-w-zeta-maxcut-boundary
  field
    selectedLiteralKernelSameElementAvailable : Bool
    kernelNinetyHeisenbergIsotypyAvailable : Bool
    barracloughWilsonDegree729SourceAlignmentAvailable : Bool
    explicitSchrodingerHZetaCandidatePaid : Bool
    explicitSchrodingerHeisenbergActionPaid : Bool
    arbitraryNonzeroCoordinateExtractionPaid : Bool
    explicitSchrodingerIrreducibilityPaid : Bool
    fixedPhaseCharacterSignatureUniquenessPaid : Bool
    genericEqualCharacterSimpleIsoLeanSourceWritten : Bool
    genericEqualCharacterSimpleIsoKernelObserved : Bool
    monsterFDRepCharacterTransportPaid : Bool
    proofRelevantRecognitionGateAvailable : Bool
    legacyTypedObligationCountsAsPaidRecognition : Bool
    proofRelevantHZetaWitnessPaid : Bool
    proofRelevantConstituentAttachmentPaid : Bool
    proofRelevantHomIntertwinerPaid : Bool
    proofRelevantMultiplicityBasisPaid : Bool
    proofRelevantCorrectedRecognitionSourcePaid : Bool
    homSpaceMultiplicityTargetReused : Bool
    suzukiMultiplicityRepresentationRouteSourcePaid : Bool
    suzukiTwelvePlusSeventyEightCandidateShapePaid : Bool
    suzukiCandidateProducerWritten : Bool
    suzukiCandidateProducerExecuted : Bool
    suzukiPairMonsterOccurrencePaid : Bool
    individualZetaMultiplicityOrientationPaid : Bool
    finiteX6Fin90BasisModelPaid : Bool
    fin90IsPrimaryMultiplicityObject : Bool
    wholeWZetaVectorCarrierBijectionToFiniteBasisRequired : Bool
    actualHZetaSameObjectRecognitionPaid : Bool
    actualHomEvaluationSameObjectPaid : Bool
    actualMultiplicityFin90BasisPaid : Bool
    representationNativeWZetaBasisActionPaid : Bool
    correctedRecognitionSourceInhabitedHere : Bool
    nextResidual : String

open CorrectedWZetaMaxCutBoundary public

canonicalBoundary : CorrectedWZetaMaxCutBoundary
canonicalBoundary =
  corrected-w-zeta-maxcut-boundary
    true
    true
    (BW.repoSchrodingerDimension729SourceAligned BW.canonicalBoundary)
    (Schrodinger.hilbertLiftPackaged Schrodinger.canonicalSchrodingerHilbertLiftBoundary)
    (Schrodinger.fullHeisenbergLinearActionPackaged Schrodinger.canonicalSchrodingerHilbertLiftBoundary)
    (Irreducibility.arbitraryNonzeroVectorYieldsSelectedNonzeroCoordinate Irreducibility.canonicalBoundary)
    (Irreducibility.schrodingerIrreducibilityPaid Irreducibility.canonicalBoundary)
    true
    (CharacterLean.leanEqualCharacterSimpleIsoSourceWritten CharacterLean.canonicalBoundary)
    (CharacterLean.leanExactHeadKernelReceiptObserved CharacterLean.canonicalBoundary)
    false
    true
    false
    false
    false
    false
    false
    false
    true
    (Suzuki.primaryTensorInductionFormulaPaid Suzuki.currentSuzukiMultiplicityFrontier)
    (Suzuki.faithfulTwelveSeventyEightPairShapeSourcePaid Suzuki.currentSuzukiMultiplicityFrontier)
    (Suzuki.faithfulTwelveSeventyEightCandidateProducerWritten Suzuki.currentSuzukiMultiplicityFrontier)
    (Suzuki.candidateProducerExecuted Suzuki.currentSuzukiMultiplicityFrontier)
    (SuzukiSame.actualRestrictedMonsterOccurrencePaid SuzukiSame.currentSuzukiMainSameObjectFrontier)
    (SuzukiSame.individualZetaAtlasLabelOrientationPaid SuzukiSame.currentSuzukiMainSameObjectFrontier)
    true
    false
    false
    false
    false
    false
    false
    false
    nextResidual
