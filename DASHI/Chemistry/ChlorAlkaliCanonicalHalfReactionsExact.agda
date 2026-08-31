module DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)

import DASHI.Chemistry.ChlorAlkaliHalfReactionExact as Half
import DASHI.Chemistry.ChlorAlkaliSaltIndustryExact as Industry
import DASHI.Chemistry.TransitionKernel as Chemistry
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
  { Chemistry.temperatureCarrier = "cell operating temperature supplied by plant receipt"
  ; Chemistry.pHCarrier = "electrode-compartment pH supplied by cell model"
  ; Chemistry.pressureCarrier = "cell/product pressure supplied by plant receipt"
  ; Chemistry.humidityCarrier = "not primary state variable"
  ; Chemistry.illuminationCarrier = "not primary state variable"
  ; Chemistry.ionicStrengthCarrier = "concentrated electrolyte model supplied by plant receipt"
  }

anodeCondition : Chemistry.Condition
anodeCondition = record
  { Chemistry.conditionLabel = "chlor-alkali anode oxidation"
  ; Chemistry.environment = halfReactionEnvironment
  ; Chemistry.guardExpression = "anode polarised; chloride-containing anolyte; cell-specific electrode obligations satisfied"
  }

cathodeCondition : Chemistry.Condition
cathodeCondition = record
  { Chemistry.conditionLabel = "chlor-alkali cathode reduction"
  ; Chemistry.environment = halfReactionEnvironment
  ; Chemistry.guardExpression = "cathode polarised; aqueous catholyte; cell-specific electrode obligations satisfied"
  }

anodeRate : Chemistry.RateLaw
anodeRate = record
  { Chemistry.rateLawKind = Chemistry.empirical
  ; Chemistry.symbolicForm = "chloride oxidation electrode kinetics supplied by cell model"
  ; Chemistry.parameters = []
  ; Chemistry.validityRegime = "chlor-alkali anode regime"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

cathodeRate : Chemistry.RateLaw
cathodeRate = record
  { Chemistry.rateLawKind = Chemistry.empirical
  ; Chemistry.symbolicForm = "water reduction electrode kinetics supplied by cell model"
  ; Chemistry.parameters = []
  ; Chemistry.validityRegime = "chlor-alkali cathode regime"
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

canonicalAnodeHalfReaction : Chemistry.Transition
canonicalAnodeHalfReaction = record
  { Chemistry.transitionId = "chlor-alkali anode: chloride oxidation"
  ; Chemistry.transitionKind = Chemistry.chemicalReaction
  ; Chemistry.reactants =
      record { Chemistry.species = Salt.chlorideIonSpecies ; Chemistry.coefficient = 2 } ∷ []
  ; Chemistry.products =
      record { Chemistry.species = Industry.chlorineGasSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = Half.electronSpecies ; Chemistry.coefficient = 2 }
      ∷ []
  ; Chemistry.catalysts = []
  ; Chemistry.rateLaw = anodeRate
  ; Chemistry.condition = anodeCondition
  ; Chemistry.reversibility = Chemistry.irreversible
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

canonicalCathodeHalfReaction : Chemistry.Transition
canonicalCathodeHalfReaction = record
  { Chemistry.transitionId = "chlor-alkali cathode: water reduction"
  ; Chemistry.transitionKind = Chemistry.chemicalReaction
  ; Chemistry.reactants =
      record { Chemistry.species = Industry.waterSpecies ; Chemistry.coefficient = 2 }
      ∷ record { Chemistry.species = Half.electronSpecies ; Chemistry.coefficient = 2 }
      ∷ []
  ; Chemistry.products =
      record { Chemistry.species = Industry.hydrogenGasSpecies ; Chemistry.coefficient = 1 }
      ∷ record { Chemistry.species = Half.hydroxideIonSpecies ; Chemistry.coefficient = 2 }
      ∷ []
  ; Chemistry.catalysts = []
  ; Chemistry.rateLaw = cathodeRate
  ; Chemistry.condition = cathodeCondition
  ; Chemistry.reversibility = Chemistry.irreversible
  ; Chemistry.evidence = Chemistry.literatureEstablished
  }

record CanonicalHalfReactionPair : Set where
  constructor canonicalHalfReactionPair
  field
    anode : Chemistry.Transition
    cathode : Chemistry.Transition
    anodeIsCanonical : anode ≡ canonicalAnodeHalfReaction
    cathodeIsCanonical : cathode ≡ canonicalCathodeHalfReaction
    anodeElectronMultiplicity : Chemistry.coefficient
      (record { Chemistry.species = Half.electronSpecies ; Chemistry.coefficient = 2 }) ≡ 2
    cathodeElectronMultiplicity : Chemistry.coefficient
      (record { Chemistry.species = Half.electronSpecies ; Chemistry.coefficient = 2 }) ≡ 2

canonicalHalfReactionPairReceipt : CanonicalHalfReactionPair
canonicalHalfReactionPairReceipt = record
  { anode = canonicalAnodeHalfReaction
  ; cathode = canonicalCathodeHalfReaction
  ; anodeIsCanonical = refl
  ; cathodeIsCanonical = refl
  ; anodeElectronMultiplicity = refl
  ; cathodeElectronMultiplicity = refl
  }
