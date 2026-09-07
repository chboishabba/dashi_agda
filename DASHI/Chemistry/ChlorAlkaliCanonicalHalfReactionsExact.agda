module DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Chemistry.ChlorAlkaliHalfReactionExact as Half
import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.TransitionKernel as Chemistry
open Chemistry
import DASHI.Geology.SaltGeochemistryExact as Salt

------------------------------------------------------------------------
-- CANONICAL CHLOR-ALKALI HALF REACTIONS
--
-- Literal reaction objects for the standard chloride-oxidation / water-
-- reduction bookkeeping used by membrane and diaphragm chlor-alkali cells.
-- Electrode kinetics, potentials and materials remain application receipts.
------------------------------------------------------------------------

halfReactionEnvironment : Chemistry.Environment
halfReactionEnvironment = record
  { temperatureCarrier = "cell operating temperature supplied by plant receipt"
  ; pHCarrier = "electrode-compartment pH supplied by cell model"
  ; pressureCarrier = "cell/product pressure supplied by plant receipt"
  ; humidityCarrier = "not primary state variable"
  ; illuminationCarrier = "not primary state variable"
  ; ionicStrengthCarrier = "concentrated electrolyte model supplied by plant receipt"
  }

anodeCondition : Chemistry.Condition
anodeCondition = record
  { conditionLabel = "chlor-alkali anode oxidation"
  ; environment = halfReactionEnvironment
  ; guardExpression = "anode polarised; chloride-containing anolyte; cell-specific electrode obligations satisfied"
  }

cathodeCondition : Chemistry.Condition
cathodeCondition = record
  { conditionLabel = "chlor-alkali cathode reduction"
  ; environment = halfReactionEnvironment
  ; guardExpression = "cathode polarised; aqueous catholyte; cell-specific electrode obligations satisfied"
  }

anodeRate : Chemistry.RateLaw
anodeRate = record
  { rateLawKind = Chemistry.empirical
  ; symbolicForm = "chloride oxidation electrode kinetics supplied by cell model"
  ; parameters = []
  ; validityRegime = "chlor-alkali anode regime"
  ; evidence = Chemistry.literatureEstablished
  }

cathodeRate : Chemistry.RateLaw
cathodeRate = record
  { rateLawKind = Chemistry.empirical
  ; symbolicForm = "water reduction electrode kinetics supplied by cell model"
  ; parameters = []
  ; validityRegime = "chlor-alkali cathode regime"
  ; evidence = Chemistry.literatureEstablished
  }

canonicalAnodeHalfReaction : Chemistry.Transition
canonicalAnodeHalfReaction = record
  { transitionId = "chlor-alkali anode: chloride oxidation"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      record { species = Salt.chlorideIonSpecies ; coefficient = 2 } ∷ []
  ; products =
      record { species = Industry.chlorineGasSpecies ; coefficient = 1 }
      ∷ record { species = Half.electronSpecies ; coefficient = 2 }
      ∷ []
  ; catalysts = []
  ; rateLaw = anodeRate
  ; condition = anodeCondition
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

canonicalCathodeHalfReaction : Chemistry.Transition
canonicalCathodeHalfReaction = record
  { transitionId = "chlor-alkali cathode: water reduction"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants =
      record { species = Industry.waterSpecies ; coefficient = 2 }
      ∷ record { species = Half.electronSpecies ; coefficient = 2 }
      ∷ []
  ; products =
      record { species = Industry.hydrogenGasSpecies ; coefficient = 1 }
      ∷ record { species = Half.hydroxideIonSpecies ; coefficient = 2 }
      ∷ []
  ; catalysts = []
  ; rateLaw = cathodeRate
  ; condition = cathodeCondition
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

record CanonicalHalfReactionPair : Set where
  constructor canonicalHalfReactionPair
  field
    anode : Chemistry.Transition
    cathode : Chemistry.Transition
    anodeIsCanonical : anode ≡ canonicalAnodeHalfReaction
    cathodeIsCanonical : cathode ≡ canonicalCathodeHalfReaction
    anodeElectronMultiplicity : Chemistry.coefficient
      (record { species = Half.electronSpecies ; coefficient = 2 }) ≡ 2
    cathodeElectronMultiplicity : Chemistry.coefficient
      (record { species = Half.electronSpecies ; coefficient = 2 }) ≡ 2

canonicalHalfReactionPairReceipt : CanonicalHalfReactionPair
canonicalHalfReactionPairReceipt = record
  { anode = canonicalAnodeHalfReaction
  ; cathode = canonicalCathodeHalfReaction
  ; anodeIsCanonical = refl
  ; cathodeIsCanonical = refl
  ; anodeElectronMultiplicity = refl
  ; cathodeElectronMultiplicity = refl
  }
