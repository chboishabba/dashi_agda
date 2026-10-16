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
-- H_zeta model side is now exhausted much further:
--   * explicit Schrodinger action;
--   * unconditional irreducibility;
--   * all 729 modulation sums checked;
--   * all 3^13 Heisenberg coordinates classified;
--   * literal character matches the canonical nonlinear zeta signature at the
--     exact executable-receipt level;
--   * a fixed-phase character compiler already turns two concretely packaged
--     irreducibles in one common theory into the required equivariant iso.
--
-- Hence the live H_zeta payment is only the ACTUAL W_zeta|E side: a
-- proof-relevant irreducible constituent decomposition plus same-object
-- action/character bindings into the common representation theory.
--
-- S_zeta uses the existing full-character GAP/CTblLib chain, but promotion is
-- now proof-relevant at every layer.  External GAP booleans/table coordinates
-- remain execution evidence rather than Agda inhabitants.
------------------------------------------------------------------------

record CurrentMonster3BMaxCut : Set where
  constructor current-monster-3b-max-cut
  field
    schrodingerExplicitActionPaid : Bool
    schrodingerIrreducibilityPaid : Bool
    all729SchrodingerCharacterSumsExecuted : Bool
    all1594323HeisenbergElementsClassified : Bool
    schrodingerSelectedCentralPhaseCharacterExecuted : Bool
    schrodingerCharacterMatchesCanonicalSignatureExecutable : Bool
    schrodingerCharacterIsAgdaKernelTheoremHere : Bool
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
  (LiteralCharacter.all729ModulationCharacterSumsVerified LiteralCharacter.canonicalBoundary)
  (LiteralCharacter.all1594323HeisenbergCoordinatesClassified LiteralCharacter.canonicalBoundary)
  (LiteralCharacter.centralZetaTrace729PaidExecutable LiteralCharacter.canonicalBoundary)
  (LiteralCharacter.literalCharacterMatchesCanonicalHeisenbergSignatureExecutable LiteralCharacter.canonicalBoundary)
  (LiteralCharacter.agdaKernelTraceDerivationPaidHere LiteralCharacter.canonicalBoundary)
  (HZetaCompiler.fixedPhaseIsoCompilerAvailable HZetaCompiler.canonicalBoundary)
  (RecognitionHardening.paidHZetaRecognitionWrapperAvailable RecognitionHardening.canonicalBoundary)
  false false false false
  true
  (SuzukiHardening.paidWholeSameObjectWrapperAvailable SuzukiHardening.canonicalBoundary)
  false false false
  (SuzukiHardening.externalGapResultCreatesAgdaProof SuzukiHardening.canonicalBoundary)
  false false
  "Construct the proof-relevant SAME actual W_zeta|E irreducible decomposition; bind one selected constituent and the explicit Schrodinger module to one common finite-group representation/character theory. The model-side irreducibility and exhaustive literal character computation are already paid at their stated authority level, and the existing fixed-phase compiler then produces the equivariant H_zeta recognition/action isomorphism. Do not add another uniqueness theorem or recompute the Schrodinger character."
  "Run the already-written CTblLib 6.Suz -> 6.Suz.2 -> quotient -> MN3B -> Monster full-character matcher in an environment with GAP/CTblLib, retain exact output/provenance, then inhabit the proof-relevant pair-family occurrence obligations and separately orient the selected zeta member. Only after that instantiate S_zeta = Hom_E(H_zeta,W_zeta) and its evaluation/recovery; Fin90 remains an optional later basis coordinate."

priorBoundary : Prior.CorrectedWZetaMaxCutBoundary
priorBoundary = Prior.canonicalBoundary
