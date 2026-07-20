module DASHI.Philosophy.ProcessOntology where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Process ontology:
--
-- void -> difference -> relation -> provisional world -> marked extension
--      -> relational extension
--
-- Numeric stages are interpretive chart labels, not metaphysical theorems.

data AbsenceKind : Set where
  emptyCarrier :
    AbsenceKind

  constitutiveGap :
    AbsenceKind

  translationLoss :
    AbsenceKind

  contextualExterior :
    AbsenceKind

  formalObstruction :
    AbsenceKind

data ProcessStage : Set where
  undifferentiatedPossibility :
    ProcessStage

  determinationCut :
    ProcessStage

  relationalEncounter :
    ProcessStage

  provisionalWorld :
    ProcessStage

  markedExtension :
    ProcessStage

  relationalExtension :
    ProcessStage

stageIndex : ProcessStage → Nat
stageIndex undifferentiatedPossibility = 0
stageIndex determinationCut = 1
stageIndex relationalEncounter = 6
stageIndex provisionalWorld = 9
stageIndex markedExtension = 10
stageIndex relationalExtension = 11

record ProcessReading : Set where
  constructor mkProcessReading
  field
    stage :
      ProcessStage

    reading :
      String

    mathematicalIdentityClaimed :
      Bool

    provisionalNotFinal :
      Bool

open ProcessReading public

canonicalProcessReadings :
  List ProcessReading
canonicalProcessReadings =
  mkProcessReading
    undifferentiatedPossibility
    "zero as no fixed determination yet"
    false
    true
  ∷
  mkProcessReading
    determinationCut
    "one as a boundary-producing determination"
    false
    true
  ∷
  mkProcessReading
    relationalEncounter
    "six as an optional chart label for tension and reflexive exchange"
    false
    true
  ∷
  mkProcessReading
    provisionalWorld
    "nine as closure relative to a declared grammar"
    false
    true
  ∷
  mkProcessReading
    markedExtension
    "ten as a marked new axis or adjoined standpoint"
    false
    true
  ∷
  mkProcessReading
    relationalExtension
    "eleven as a marked relation rather than numerical destiny"
    false
    true
  ∷ []

nineIsProvisional :
  provisionalNotFinal
    (mkProcessReading
      provisionalWorld
      "nine as closure relative to a declared grammar"
      false
      true)
  ≡
  true
nineIsProvisional =
  refl

tenIndexIsTen :
  stageIndex markedExtension ≡ 10
tenIndexIsTen =
  refl

elevenIndexIsEleven :
  stageIndex relationalExtension ≡ 11
elevenIndexIsEleven =
  refl
