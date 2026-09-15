module DASHI.Moonshine.Base369Monster3BShortestFrontierCandidateCompilerExact where

open import DASHI.Core.Prelude
open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Moonshine.MonsterGradedVOAActual3BKernelSameElementBidiExact as KernelWeld
import DASHI.Moonshine.Base369Monster3BRecognitionCompletionCompilerExact as Completion
import DASHI.Moonshine.Base369Monster3BShortestFrontierCapstoneBidiExact as Capstone

------------------------------------------------------------------------
-- BASE369 CANDIDATE -> SHORTEST MONSTER-3B FRONTIER COMPILER
--
-- The existing capstone takes two external payments:
--
--   (1) a selected literal Monster element attached to the certified central
--       3B kernel class;
--   (2) ActualZetaSectorRecognition on that exact literal zeta eigenspace.
--
-- The new recognition-completion compiler shows that payment (2) may be
-- supplied in a native Base369 presentation instead:
--
--   selected literal W_zeta
--      <-> appraisal-fibre x Fin90
--
-- with six translation and six modulation-exponent intertwiners.  The exact
-- existing Base369 <-> X6 chart then compiles this into the capstone's stronger
-- ActualZetaSectorRecognition input.
--
-- Nothing in this file constructs the external candidate or kernel attachment.
-- Character isotypy, 65610=729*90, OEIS/QID coordinates and carrier cardinality
-- remain insufficient.
------------------------------------------------------------------------

record Shortest3BBase369CandidateSource (Monster K : Set) : Setω where
  field
    attachment : KernelWeld.Actual3BKernelSameElementAttachment Monster K

    base369RecognitionCandidate :
      Completion.Base369RecognitionCandidate
        (KernelWeld.selectedLiteralZetaSector attachment)

open Shortest3BBase369CandidateSource public

compileShortestFrontierSource :
  ∀ {Monster K} →
  Shortest3BBase369CandidateSource Monster K →
  Capstone.Shortest3BFrontierSource Monster K
compileShortestFrontierSource source = record
  { attachment = attachment source
  ; recognition =
      Completion.compileBase369Recognition
        (base369RecognitionCandidate source)
  }

------------------------------------------------------------------------
-- The existing capstone tail is now available from the smaller native input.
------------------------------------------------------------------------

compiledCentralZetaAmplitudeIs65610 :
  ∀ {Monster K}
    (source : Shortest3BBase369CandidateSource Monster K) →
  _
compiledCentralZetaAmplitudeIs65610 source =
  Capstone.selectedCentralZetaAmplitudeIs65610
    (compileShortestFrontierSource source)

compiledKernelMultiplicityIsNinety :
  ∀ {Monster K}
    (source : Shortest3BBase369CandidateSource Monster K) →
  _
compiledKernelMultiplicityIsNinety source =
  Capstone.selectedKernelMultiplicityIsNinety
    (compileShortestFrontierSource source)

------------------------------------------------------------------------
-- WrongType / attribution firewalls.
------------------------------------------------------------------------

data CharacterIsotypyCreatesBase369Candidate : Set where
data DimensionCreatesBase369Candidate : Set where
data OEISCreatesBase369Candidate : Set where
data QIDCreatesBase369Candidate : Set where

characterIsotypyDoesNotCreateBase369Candidate :
  CharacterIsotypyCreatesBase369Candidate → ⊥
characterIsotypyDoesNotCreateBase369Candidate ()

dimensionDoesNotCreateBase369Candidate : DimensionCreatesBase369Candidate → ⊥
dimensionDoesNotCreateBase369Candidate ()

oeisDoesNotCreateBase369Candidate : OEISCreatesBase369Candidate → ⊥
oeisDoesNotCreateBase369Candidate ()

qidDoesNotCreateBase369Candidate : QIDCreatesBase369Candidate → ⊥
qidDoesNotCreateBase369Candidate ()

------------------------------------------------------------------------
-- Frontier.
------------------------------------------------------------------------

nextResidual : String
nextResidual =
  "inhabit Shortest3BBase369CandidateSource on the exact selected literal 3B source: retain the certified central-zeta kernel attachment and acquire a Base369RecognitionCandidate for that same literal W_zeta sector. The existing reverse compiler then produces ActualZetaSectorRecognition and the capstone generates all X6/Fin90 coordinates and appraisal-slice consequences. Character isotypy, 65610=729*90, OEIS/QID/Dewey/Wikipedia and bare carrier cardinality do not create the candidate."

record Base369ShortestFrontierCandidateBoundary : Set where
  constructor base369-shortest-frontier-candidate-boundary
  field
    selectedKernelAttachmentRetained : Bool
    base369CandidateCompilesRecognition : Bool
    capstoneTailBecomesCompilerOutput : Bool
    base369CandidateInhabitedHere : Bool
    characterIsotypyCreatesCandidate : Bool
    oeisCreatesCandidate : Bool
    nextResidual : String
open Base369ShortestFrontierCandidateBoundary public

canonicalBase369ShortestFrontierCandidateBoundary :
  Base369ShortestFrontierCandidateBoundary
canonicalBase369ShortestFrontierCandidateBoundary =
  base369-shortest-frontier-candidate-boundary
    true true true
    false false false
    nextResidual
