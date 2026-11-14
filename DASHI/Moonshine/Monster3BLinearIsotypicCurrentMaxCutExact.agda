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
-- * canonical normalizer action on Hom_E(H,W);
-- * a proof-bearing compiler from an actual 196883-dimensional Griess
--   representation + injective equivariant grade-two inclusion to the legacy
--   `WeightTwoLinearActionBridge` and its paid proof-relevant wrapper.
--
-- The remaining Monster frontier is therefore same-object SOURCE/ACTION
-- attachment, not more abstract representation plumbing and not bare dimension
-- or character arithmetic.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Irr
import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as Character
import DASHI.Moonshine.Monster3BActualLinearIsotypicTerminalCompilerExact as Terminal
import DASHI.Moonshine.MonsterWeightTwoGriessConstituentCompilerExact as Griess
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

    proofBearingGriessConstituentCompilerSourceWritten : Bool
    actualGriess196883RepresentationWitnessPaid : Bool
    actualGriessInjectiveEquivariantInclusionPaid : Bool

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
  Griess.griessCompilerProducesPaidBridge
  false false
  false false false false false false false
  (Phase1278.selectedPhase8748CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase56862CharacterFamilyPaid Phase1278.currentPhaseCharacterWeldFrontier)
  (Phase1278.selectedPhase65610DegreePaid Phase1278.currentPhaseCharacterWeldFrontier)
  false false false false false false false false false
  false
  "The abstract representation tail is exhausted at source level. For the requested Griess closure, instantiate MonsterWeightTwoGriessConstituentCompilerExact.GriessConstituentLinearWitness with an ACTUAL Monster finite-dimensional representation of declared dimension 196883, a proof-bearing linear realisation, and an injective equivariant inclusion into the SAME literal grade-two representation. The compiler then produces WeightTwoLinearActionBridge and PaidWeightTwoLinearActionBridge automatically. Character identities, 65610=90*729, the 12+78 family split, the finite SemanticMonsterConstituent196883 basis-label carrier, and the fixed conformal point do not create that representation or inclusion. After this same-object linear packet is paid, transport chi(W_zeta|E)=90 chi(H_zeta) onto the exact FDRep objects; classifier, Maschke, isotypy, n=90, Schur multiplicity coordinates and tensor evaluation are downstream compilers. For multiplicity action, use actual normalizer/projective lifts on H_zeta and W_zeta; the Hom action is canonical, then transport the selected-phase 12+78 character and orient zeta. Fin90 remains downstream coordinates only."

irreducibilityBoundary : Irr.Boundary
irreducibilityBoundary = Irr.canonicalBoundary

characterBoundary : Character.Boundary
characterBoundary = Character.canonicalBoundary
