module DASHI.Biology.Molecular.BH4RheaChEBIReactionExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

------------------------------------------------------------------------
-- RHEA / ChEBI biochemical reaction identity owner.
--
-- Source calibration (acquired/inspected 2026-10-17):
--   Rhea release 142 / 2026-09-02, SPARQL release label 2026_03.
--   RHEA:17869 generic dihydropteridine reductase quartet.
--   RHEA:32253 specific right-to-left physiological child:
--     (6R)-L-erythro-6,7-dihydrobiopterin + NADH + H+
--       => (6R)-L-erythro-5,6,7,8-tetrahydrobiopterin + NAD+.
--
-- Rhea uses ChEBI major microspecies for chemically balanced reactions.  The
-- exact reaction microspecies and broader ontology coordinates are therefore
-- kept separate rather than silently collapsed.
------------------------------------------------------------------------

data ReactionDirection : Set where
  undefinedDirection : ReactionDirection
  leftToRight : ReactionDirection
  rightToLeft : ReactionDirection
  bidirectional : ReactionDirection

data ReactionSide : Set where
  substrateSide : ReactionSide
  productSide : ReactionSide

record ChemicalParticipant : Set where
  constructor chemicalParticipant
  field
    chebiId : String
    broaderChebiId : String
    name : String
    formula : String
    integerCharge : String
    coefficient : Nat
    side : ReactionSide
    exactMicrospecies : Bool

open ChemicalParticipant public

record RheaReactionReceipt : Set where
  constructor rheaReactionReceipt
  field
    rheaId : String
    directedRheaId : String
    specificDirectedRheaId : String
    equation : String
    direction : ReactionDirection
    participants : List ChemicalParticipant
    chemicallyBalancedByRhea : Bool
    releaseReference : String
    sourceReference : String
    reactionIdentityCreatesBiologicalMechanism : Bool

open RheaReactionReceipt public

qdprDihydrobiopterin : ChemicalParticipant
qdprDihydrobiopterin = chemicalParticipant
  "CHEBI:43120" "CHEBI:20680"
  "(6R)-L-erythro-6,7-dihydrobiopterin"
  "C9H13N5O3" "0" 1 substrateSide true

qdprNADH : ChemicalParticipant
qdprNADH = chemicalParticipant
  "CHEBI:57945" "CHEBI:57945"
  "NADH" "C21H27N7O14P2" "-2" 1 substrateSide true

qdprProton : ChemicalParticipant
qdprProton = chemicalParticipant
  "CHEBI:15378" "CHEBI:15378"
  "H+" "H" "+1" 1 substrateSide true

qdprBH4 : ChemicalParticipant
qdprBH4 = chemicalParticipant
  "CHEBI:59560" "CHEBI:15372"
  "(6R)-L-erythro-5,6,7,8-tetrahydrobiopterin"
  "C9H15N5O3" "0" 1 productSide true

qdprNADPlus : ChemicalParticipant
qdprNADPlus = chemicalParticipant
  "CHEBI:57540" "CHEBI:57540"
  "NAD+" "C21H26N7O14P2" "-1" 1 productSide true

qdprParticipants : List ChemicalParticipant
qdprParticipants =
  qdprDihydrobiopterin ∷ qdprNADH ∷ qdprProton
  ∷ qdprBH4 ∷ qdprNADPlus ∷ []

qdprGenericReaction : RheaReactionReceipt
qdprGenericReaction = rheaReactionReceipt
  "RHEA:17869"
  "RHEA:17871"
  "RHEA:32253"
  "(6R)-L-erythro-6,7-dihydrobiopterin + NADH + H+ => (6R)-L-erythro-5,6,7,8-tetrahydrobiopterin + NAD+"
  rightToLeft
  qdprParticipants
  true
  "Rhea release 142 (2026-09-02); SPARQL release 2026_03"
  "https://www.rhea-db.org/rhea/32253; ChEBI participants as used by Rhea"
  false

record RheaChEBIBoundary : Set where
  constructor rhea-chebi-boundary
  field
    reactionIdentityCreatesBiologicalMechanism : Bool
    reactionIdentityCreatesBiologicalMechanismIsFalse :
      reactionIdentityCreatesBiologicalMechanism ≡ false
    exactMicrospeciesEqualsEveryOntologyParent : Bool
    exactMicrospeciesEqualsEveryOntologyParentIsFalse :
      exactMicrospeciesEqualsEveryOntologyParent ≡ false
    rheaBalancedCreatesMeasuredFlux : Bool
    rheaBalancedCreatesMeasuredFluxIsFalse : rheaBalancedCreatesMeasuredFlux ≡ false

canonicalRheaChEBIBoundary : RheaChEBIBoundary
canonicalRheaChEBIBoundary = rhea-chebi-boundary false refl false refl false refl

canonicalBH4RheaChEBIReceipt : Receipt.GenericReceipt
canonicalBH4RheaChEBIReceipt =
  Receipt.mkNonPromotingReceipt
    "BH4 Rhea/ChEBI reaction identity"
    "DASHI.Biology.Molecular.BH4RheaChEBIReactionExact"
    "RHEA:17869 / RHEA:17871 / RHEA:32253 with exact ChEBI reaction microspecies"
    "pays bounded QDPR reaction identity, direction, participant formula/charge coordinates and Rhea chemical-balance status"
    "reaction identity and database balance do not create kinetics, measured flux, compartment state, allocator competition, biological mechanism or disease causation"
    "python3 scripts/acquire_rhea_chebi_bh4_reactions.py --qdpr"
