module DASHI.Culture.ShakespeareLiteraryTopologyBridgeExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Reasoning.StructuralTransferBreakdownExact as Breakdown
import DASHI.Reasoning.StructuralMetaphorSourceRegistryExact as Sources

------------------------------------------------------------------------
-- SHAKESPEARE / LITERARY-TOPOLOGY INTERPRETIVE BRIDGE
--
-- Primary methodological source:
--   Nusrat Fatima (2026), "Continuity and Its Limits: Toward a Critical Theory
--   of Literary Topology in Shakespeare", Journal of Critical Studies in
--   Language and Literature 7(2):1-8, DOI 10.46809/jcsll.v7i2.430.
--
-- Fatima explicitly foregrounds The Winter's Tale and King Lear as the
-- romance/tragedy contrast.  The remaining popular-play classifications below
-- are DASHI interpretive extensions, keyed to act/scene anchors so the claims
-- remain auditable rather than floating literary slogans.
------------------------------------------------------------------------

data Play : Set where
  wintersTale tempest twelfthNight midsummer
  romeoAndJuliet hamlet macbeth kingLear : Play

data ElasticityClass : Set where
  highlyRecoverable deformedButRecoverable mixedContracting terminalRupture
  : ElasticityClass

elasticity : Play → ElasticityClass
elasticity wintersTale = deformedButRecoverable
elasticity tempest = deformedButRecoverable
elasticity twelfthNight = highlyRecoverable
elasticity midsummer = highlyRecoverable
elasticity romeoAndJuliet = terminalRupture
elasticity hamlet = mixedContracting
elasticity macbeth = mixedContracting
elasticity kingLear = terminalRupture

record ShakespeareAnchor : Set where
  constructor shakespeareAnchor
  field
    play : Play
    actScene : String
    structuralUse : String

open ShakespeareAnchor public

-- Act/scene anchors only: no claim that the short descriptions are quotations.
-- The Winter's Tale: accusation/judgment and the statue recognition scene.
wintersTaleAccusation : ShakespeareAnchor
wintersTaleAccusation =
  shakespeareAnchor wintersTale "3.2"
    "Loss and accusation deform the kinship structure before the long interval."

wintersTaleReturn : ShakespeareAnchor
wintersTaleReturn =
  shakespeareAnchor wintersTale "5.3"
    "Recognition/restoration returns relation in a transformed state rather than resetting history."

-- The Tempest: Prospero's account of exile and the final renunciation/reunion.
tempestExile : ShakespeareAnchor
tempestExile =
  shakespeareAnchor tempest "1.2"
    "Past betrayal and exile remain necessary provenance for the island's present relational order."

tempestReturn : ShakespeareAnchor
tempestReturn =
  shakespeareAnchor tempest "5.1"
    "Political and familial relations are reconfigured before Prospero's return."

-- Twelfth Night: shipwreck/disguise and final recognition.
twelfthNightDisguise : ShakespeareAnchor
twelfthNightDisguise =
  shakespeareAnchor twelfthNight "1.2"
    "Viola's public social presentation changes while fine identity/history is retained."

twelfthNightRecognition : ShakespeareAnchor
twelfthNightRecognition =
  shakespeareAnchor twelfthNight "5.1"
    "Recognition recovers identity relations without erasing the disguised interval."

-- A Midsummer Night's Dream: desire relations are rewritten and later restored.
midsummerRewire : ShakespeareAnchor
midsummerRewire =
  shakespeareAnchor midsummer "2.2"
    "The same persons acquire changed desire relations under enchantment."

midsummerRestore : ShakespeareAnchor
midsummerRestore =
  shakespeareAnchor midsummer "4.1"
    "The altered relational graph remains recoverable enough for comic reconstruction."

-- Romeo and Juliet: terminal tomb scene.
romeoJulietTerminal : ShakespeareAnchor
romeoJulietTerminal =
  shakespeareAnchor romeoAndJuliet "5.3"
    "The lovers' central relation terminates; later family reconciliation does not repair that relation."

-- Hamlet: provenance claim, Mousetrap perturbation, terminal contraction.
hamletGhost : ShakespeareAnchor
hamletGhost =
  shakespeareAnchor hamlet "1.5"
    "A hidden causal history is supplied as a hypothesis about the coarse present political state."

hamletMousetrap : ShakespeareAnchor
hamletMousetrap =
  shakespeareAnchor hamlet "3.2"
    "Hamlet introduces a perturbation/observation step to test the provenance hypothesis."

hamletTerminal : ShakespeareAnchor
hamletTerminal =
  shakespeareAnchor hamlet "5.2"
    "Recognition and decision occur after the viable social future has sharply contracted."

-- Macbeth: regicide and the later self-reinforcing action landscape.
macbethRegicide : ShakespeareAnchor
macbethRegicide =
  shakespeareAnchor macbeth "2.2"
    "Regicide changes the later option landscape by creating concealment, succession, and legitimacy dependencies."

macbethBanquo : ShakespeareAnchor
macbethBanquo =
  shakespeareAnchor macbeth "3.1"
    "A prior act generates further action pressure rather than remaining passive historical explanation."

-- King Lear: opening coarse-graining and terminal non-repair.
learLoveTest : ShakespeareAnchor
learLoveTest =
  shakespeareAnchor kingLear "1.1"
    "Lear projects relational fidelity onto public verbal performance and territorial allocation."

learTerminal : ShakespeareAnchor
learTerminal =
  shakespeareAnchor kingLear "5.3"
    "Late epistemic recognition does not restore the destroyed relational future."

canonicalShakespeareAnchors : List ShakespeareAnchor
canonicalShakespeareAnchors =
  wintersTaleAccusation ∷ wintersTaleReturn
  ∷ tempestExile ∷ tempestReturn
  ∷ twelfthNightDisguise ∷ twelfthNightRecognition
  ∷ midsummerRewire ∷ midsummerRestore
  ∷ romeoJulietTerminal
  ∷ hamletGhost ∷ hamletMousetrap ∷ hamletTerminal
  ∷ macbethRegicide ∷ macbethBanquo
  ∷ learLoveTest ∷ learTerminal
  ∷ []

------------------------------------------------------------------------
-- Winter's Tale / Lear finite transfer specimen.
------------------------------------------------------------------------

data TopologyFrame : Set where
  continuityDeformationReturn : TopologyFrame

data NarrativeTarget : Set where
  wintersTaleTarget kingLearTarget : NarrativeTarget

data NarrativeInvariant : Set where
  retraceableRelation irrecoverableRelation : NarrativeInvariant

data Recoverable : NarrativeTarget → Set where
  wintersTaleRecoverable : Recoverable wintersTaleTarget

data Ruptured : NarrativeTarget → Set where
  kingLearRuptured : Ruptured kingLearTarget

status : TopologyFrame → NarrativeTarget → Breakdown.TransferStatus
status continuityDeformationReturn wintersTaleTarget = Breakdown.structurallyFitting
status continuityDeformationReturn kingLearTarget = Breakdown.structurallyBroken

invariant : NarrativeTarget → NarrativeInvariant
invariant wintersTaleTarget = retraceableRelation
invariant kingLearTarget = irrecoverableRelation

shakespeareTransferSurface : Breakdown.StructuralTransferSurface
shakespeareTransferSurface =
  record
    { SourceFrame = TopologyFrame
    ; Target = NarrativeTarget
    ; Invariant = NarrativeInvariant
    ; transferStatus = status
    ; invariantAt = invariant
    ; recoverable = Recoverable
    ; ruptured = Ruptured
    ; surfaceReading =
        "Fatima's bounded literary-topology contrast: recoverable deformation is structurally compatible with the frame; terminal rupture marks its limit."
    }

fatimaRomanceFit : Breakdown.FitWitness shakespeareTransferSurface
fatimaRomanceFit =
  record
    { fitFrame = continuityDeformationReturn
    ; fitTarget = wintersTaleTarget
    ; fitStatus = refl
    ; fitRecoverable = wintersTaleRecoverable
    }

fatimaTragedyBreak : Breakdown.RuptureWitness shakespeareTransferSurface
fatimaTragedyBreak =
  record
    { ruptureFrame = continuityDeformationReturn
    ; ruptureTarget = kingLearTarget
    ; ruptureStatus = refl
    ; ruptureReceipt = kingLearRuptured
    }

fatimaUsefulHereBreaksThere : Breakdown.FitHereBreaksThere shakespeareTransferSurface
fatimaUsefulHereBreaksThere =
  record
    { fitting = fatimaRomanceFit
    ; broken = fatimaTragedyBreak
    }

------------------------------------------------------------------------
-- Genre-level interpretive summaries: DASHI extension, not Fatima quotations.
------------------------------------------------------------------------

comedyQuestion : String
comedyQuestion =
  "How far can relation deform while remaining recoverable enough for return?"

romanceQuestion : String
romanceQuestion =
  "How does retained history transform what returns, so that return is not reset?"

tragedyQuestion : String
tragedyQuestion =
  "What follows when the relation required for return has become irrecoverable?"

------------------------------------------------------------------------
-- Attribution boundary.
------------------------------------------------------------------------

fatimaSource : Sources.SourceReference
fatimaSource = Sources.fatima2026

record ShakespeareLiteraryTopologyBoundary : Set where
  constructor shakespeareLiteraryTopologyBoundary
  field
    fatimaExplicitlyAnalyzesAllEightPlayMappings : Bool
    fatimaExplicitlyAnalyzesAllEightPlayMappingsIsFalse :
      fatimaExplicitlyAnalyzesAllEightPlayMappings ≡ false

    wintersTaleAndLearAreFatimasRepresentativePoles : Bool
    wintersTaleAndLearAreFatimasRepresentativePolesIsTrue :
      wintersTaleAndLearAreFatimasRepresentativePoles ≡ true

    returnMeansReset : Bool
    returnMeansResetIsFalse : returnMeansReset ≡ false

    epistemicCorrectionGuaranteesStructuralRepair : Bool
    epistemicCorrectionGuaranteesStructuralRepairIsFalse :
      epistemicCorrectionGuaranteesStructuralRepair ≡ false

    tragedyDisprovesMathematicalTopology : Bool
    tragedyDisprovesMathematicalTopologyIsFalse :
      tragedyDisprovesMathematicalTopology ≡ false

    literaryTopologyIsUniversalMasterMethod : Bool
    literaryTopologyIsUniversalMasterMethodIsFalse :
      literaryTopologyIsUniversalMasterMethod ≡ false

canonicalShakespeareLiteraryTopologyBoundary : ShakespeareLiteraryTopologyBoundary
canonicalShakespeareLiteraryTopologyBoundary =
  shakespeareLiteraryTopologyBoundary
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
