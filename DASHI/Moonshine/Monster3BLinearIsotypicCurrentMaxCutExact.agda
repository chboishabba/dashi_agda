module DASHI.Moonshine.Monster3BLinearIsotypicCurrentMaxCutExact where

------------------------------------------------------------------------
-- CURRENT MONSTER 3B LINEAR / ISOTYPIC MAX-CUT
--
-- The reusable mathematics is now source-written through:
--
-- * invariant-subspace and literal central-eigenspace restriction;
-- * FDRep/group-algebra same-action transport;
-- * whole-character simple-source classification;
-- * Maschke semisimplicity and character-at-identity dimension ratios;
-- * Schur scalar self-intertwiners;
-- * one-type isotypy, n=90 and Hom coordinates;
-- * tensor finite-copy evaluation;
-- * two-simple (12+78) character multiplicity determination;
-- * canonical normalizer action on Hom_E(H,W).
--
-- The remaining Monster frontier is therefore same-object SOURCE/ACTION
-- attachment, not more abstract representation plumbing.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Irr
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Character
import DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact as Terminal
import DASHI.Wikimedia.IbrahimMonster3BPhaseResolvedCharacterTwelveSeventyEightWeldExact as Phase1278

record Boundary : Set where
  constructor boundary
  field
    schrodingerActionOwned : Bool
    schrodingerIrreducibilityPaid : Bool
    schrodingerLiteralCharacterExecutablePaid : Bool

    genericRestrictionTailSourceWritten : Bool
    genericWholeCharacterTailSourceWritten : Bool
    genericMaschkeSchurTailSourceWritten : Bool
    genericIsotypicNinetyHomTailSourceWritten : Bool
    genericTensorTailSourceWritten : Bool
    genericTwelveSeventyEightCharacterTailSourceWritten : Bool
    genericNormalizerHomActionSourceWritten : Bool

    arbitrarySimpleClassifierStillIndependentInput : Bool
    semisimplicityStillIndependentInput : Bool
    separateFinrankRatioStillIndependentInput : Bool
    schurStillIndependentInput : Bool
    tensorEvaluationStillIndependentInput : Bool
    twelveSeventyEightIntertwinerStillIndependentInput : Bool
    multiplicityNormalizerActionStillIndependentThirdCarrierInput : Bool

    selectedPhaseTwelveCharacterFamilyPaid : Bool
    selectedPhaseSeventyEightCharacterFamilyPaid : Bool
    selectedPhaseTotalDegree65610Paid : Bool

    actualMonsterLinearInputPacketInhabited : Bool
    actualWZetaHZetaFDRepAttachmentsPaid : Bool
    actualKernelNinetyCharacterTransportPaid : Bool
    actualWholeSectorIsotypicEquivalencePaid : Bool
    actualCopyCountNinetyPaid : Bool
    actualNormalizerLiftsOnHZetaWZetaPaid : Bool
    actualProjectiveCocycleLawsPaid : Bool
    absoluteZetaOrientationPaid : Bool
    actualSelectedPhaseTwelveSeventyEightCharacterTransportPaid : Bool

    fin90BasisNeededBeforeRepresentationRecognition : Bool
    nextResidual : String
open Boundary public

canonicalBoundary : Boundary
canonicalBoundary = boundary
  true true true
  true true true true true true true
  false false false false false false false
  (Phase1278.selectedPhase8748CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase56862CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase65610DegreePaid Phase1278.currentPhaseCharacterWeldFrontier)
  false false false false false false false false false
  false
  "The abstract representation tail is exhausted at source level. The H_zeta/W_zeta seam is now one same-object linear attachment plus transport of the certified actual-kernel identity chi(W_zeta|E)=90 chi(H_zeta) onto those exact FDRep objects. That makes classifier, Maschke, n=90, Schur multiplicity coordinates and tensor evaluation downstream compilers. For the multiplicity action, do not postulate an independent S_zeta action: supply the actual normalizer/projective lifts on H_zeta and W_zeta with their conjugation/cocycle laws; the Hom action is canonical. Then transport the already-paid selected-phase 12+78 character onto that induced Hom action and orient zeta. The generic character compiler determines the 12+78 representation decomposition. Fin90 remains downstream coordinates only."

irreducibilityBoundary : Irr.Boundary
irreducibilityBoundary = Irr.canonicalBoundary

characterBoundary : Character.Boundary
characterBoundary = Character.canonicalBoundary
