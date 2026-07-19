module DASHI.Biology.Levin.MicrobiomeHostAppetiteBoundary where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Biology.Levin.ProblemSpaceAgency as Problem
import DASHI.Biology.Levin.ConstitutiveInteractiveAutonomy as Autonomy
import DASHI.Biology.Levin.ElectrochemicalBodyConsortium as Consortium

record AppetiteSignalRoute : Set where
  field
    nutrientState : Bool
    gutMechanicalState : Bool
    enteroendocrineSignal : Bool
    vagalOrNeuralRoute : Bool
    immuneRoute : Bool
    microbialMetaboliteRoute : Bool
    learnedCueRoute : Bool
    hedonicRewardRoute : Bool
    routeInterventionsSpecified : Bool

record MicrobiomeHostAppetiteBoundary : Set where
  field
    problemSpaceBoundary : Problem.ProblemSpaceAgencyBoundary
    autonomyBoundary : Autonomy.AutonomyBoundary
    consortiumBoundary : Consortium.ElectrochemicalBodyConsortiumBoundary
    signallingIsBidirectional : Bool
    microbialMetabolitesMayAlterAppetite : Bool
    hostStateMayAlterMicrobiota : Bool
    appetiteNotOwnedByMicrobiota : Bool
    cravingNotDirectReadoutOfMicrobialGoal : Bool
    animalEvidenceNotAutomaticHumanCausality : Bool
    interpretation : String

canonicalMicrobiomeHostAppetiteBoundary : MicrobiomeHostAppetiteBoundary
canonicalMicrobiomeHostAppetiteBoundary = record
  { problemSpaceBoundary = Problem.canonicalProblemSpaceAgencyBoundary
  ; autonomyBoundary = Autonomy.canonicalAutonomyBoundary
  ; consortiumBoundary = Consortium.canonicalElectrochemicalBodyConsortiumBoundary
  ; signallingIsBidirectional = true
  ; microbialMetabolitesMayAlterAppetite = true
  ; hostStateMayAlterMicrobiota = true
  ; appetiteNotOwnedByMicrobiota = true
  ; cravingNotDirectReadoutOfMicrobialGoal = true
  ; animalEvidenceNotAutomaticHumanCausality = true
  ; interpretation = "Eating behaviour is produced by bidirectional host-microbiota signalling across nutrient, mechanical, endocrine, neural, immune, learned and hedonic routes; microbial influence is real without making appetite a command issued by a single microbial agent"
  }
