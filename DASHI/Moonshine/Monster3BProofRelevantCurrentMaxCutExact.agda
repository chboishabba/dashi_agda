module DASHI.Moonshine.Monster3BProofRelevantCurrentMaxCutExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Moonshine.Monster3BSchrodingerLiteralCharacterReceiptExact as LiteralCharacter
import DASHI.Moonshine.Monster3BFiniteStoneVonNeumannIrreducibilityClosureExact as Irreducibility
import DASHI.Moonshine.Monster3BHZetaCharacterTransportCompilerExact as HZetaCompiler
import DASHI.Moonshine.Monster3BProofRelevantRecognitionHardeningExact as RecognitionHardening
import DASHI.Moonshine.Monster3BSuzukiProofRelevantOccurrenceHardeningExact as SuzukiHardening
import DASHI.Reasoning.Trialectic369Monster3BWZetaBasisVectorMaxCutExact as Prior

------------------------------------------------------------------------
-- POST-CHARACTER / POST-PROOF-RELEVANCE MONSTER 3B MAX-CUT
--
-- Two formerly broad obligations have now collapsed to concrete same-object
-- inputs:
--
-- H_zeta:
--   * explicit Schrodinger action exists;
--   * unconditional irreducibility exists;
--   * literal character is exhaustively computed on all 3^13 Heisenberg
--     elements by the executable producer;
--   * the fixed-phase character compiler already turns a common-theory pair of
--     irreducibles into the required equivariant H_zeta isomorphism.
--
-- Therefore the live H_zeta payment is ONLY the actual W_zeta|E side:
-- construct a proof-relevant irreducible constituent of the same restricted
-- sector and bind its action/character into the common representation theory.
--
-- S_zeta:
--   the existing GAP/CTblLib matcher is already full-character/same-table
--   oriented, but its historical Agda receipt stores decisive obligations as
--   Set-valued types.  The Suzuki hardening owner now requires inhabitants at
--   every level: pair restriction, main split, quotient descent, actual
--   Monster occurrence, same-object identity and individual zeta orientation.
--   An external GAP `true` is execution evidence, not an Agda proof term.
------------------------------------------------------------------------

record CurrentMonster3BMaxCut : Set where
  constructor current-monster-3b-max-cut
  field
    schrodingerExplicitActionPaid : Bool
    schrodingerIrreducibilityPaid : Bool
    schrodingerLiteralCharacterExhaustivelyExecuted : Bool
    schrodingerSelectedCentralPhaseCharacterExecuted : Bool
    hZetaFixedPhaseIsoCompilerAvailable : Bool
    proofRelevantHZetaGateAvailable : Bool

    actualWZetaIrreducibleConstituentDecompositionPaid : Bool
    actualConstituentSameObjectActionBindingPaid : Bool
    actualConstituentCharacterBindingPaid : Bool
    actualHZetaRecognitionPaid : Bool

    suzukiFullCharacterMatcherWritten : Bool
    suzukiProofRelevantOccurrenceGateAvailable : Bool
    suzukiMatcherExecutedHere : Bool
    suzukiPairFamilyOccurrencePaidInAgda : Bool
    suzukiIndividualZetaOrientationPaidInAgda : Bool
    externalGapBooleanCreatesAgdaProof : Bool

    actualHomEvaluationPaid : Bool
    representationNativeFin90BasisPaid : Bool

    nextHZetaWall : String
    nextSZetaWall : String
open CurrentMonster3BMaxCut public

currentMonster3BMaxCut : CurrentMonster3BMaxCut
currentMonster3BMaxCut = current-monster-3b-max-cut
  true
  (Irreducibility.schrodingerIrreducibilityPaid Irreducibility.canonicalBoundary)
  (LiteralCharacter.exhaustiveGroupEnumerationCompleted LiteralCharacter.canonicalBoundary)
  true
  (HZetaCompiler.fixedPhaseIsoCompilerAvailable HZetaCompiler.canonicalBoundary)
  (RecognitionHardening.paidHZetaRecognitionWrapperAvailable RecognitionHardening.canonicalBoundary)
  false false false false
  true
  (SuzukiHardening.paidWholeSameObjectWrapperAvailable SuzukiHardening.canonicalBoundary)
  false false false
  (SuzukiHardening.externalGapResultCreatesAgdaProof SuzukiHardening.canonicalBoundary)
  false false
  "Construct the proof-relevant SAME actual W_zeta|E irreducible decomposition; bind one selected constituent and the explicit Schrodinger module to one common finite-group representation/character theory. The model-side irreducibility and literal character calculation are already paid, and the existing fixed-phase compiler then produces the equivariant H_zeta recognition/action isomorphism. Do not add another uniqueness theorem or recompute the Schrodinger character."
  "Run the already-written CTblLib 6.Suz -> 6.Suz.2 -> quotient -> MN3B -> Monster full-character matcher in an environment with GAP/CTblLib, retain its exact output/provenance, then inhabit the proof-relevant pair-family occurrence obligations and separately orient the selected zeta member. Only after that instantiate S_zeta = Hom_E(H_zeta,W_zeta) and its evaluation/recovery; Fin90 remains an optional later basis coordinate."

priorBoundary : Prior.CorrectedWZetaMaxCutBoundary
priorBoundary = Prior.canonicalBoundary
