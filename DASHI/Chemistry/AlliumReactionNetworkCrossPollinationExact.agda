module DASHI.Chemistry.AlliumReactionNetworkCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as TK
import DASHI.Chemistry.AlliumMolecularIdentityExact as Identity

------------------------------------------------------------------------
-- ALLIUM REACTION-NETWORK CROSS-POLLINATION
--
-- This translates database-level molecular identities and biochemical pathway
-- receipts into the existing generic chemistry TransitionKernel. Rates remain
-- unresolved unless separately measured in the relevant preparation.
--
-- Pathway anchors:
--   Borlinghaus et al. 2014 PMID 25153873
--   Shimon et al. 2007 PMID 17174334
--   alliinase: alliin -> allyl sulfenic acid + pyruvate + ammonia;
--   two allyl sulfenic-acid molecules then condense nonenzymatically to allicin.
--
-- Allicin-thiol anchor:
--   Borlinghaus et al. 2021 PMID 33801955.
--   Allicin reacts rapidly with GSH and accessible protein cysteine thiols by
--   S-thioallylation / thiol-disulfide-exchange-like chemistry.
------------------------------------------------------------------------

literatureSpecies : String → String → String → TK.Species
literatureSpecies sid formula role = record
  { speciesId = sid
  ; phase = TK.dissolved
  ; chargeLabel = "context dependent / unresolved"
  ; compositionLabel = formula
  ; mobilityClass = TK.mobile
  ; activityModelLabel = "activity model unresolved"
  ; opticalRoleLabel = role
  ; evidence = TK.literatureEstablished
  }

alliinSpecies : TK.Species
alliinSpecies = literatureSpecies
  "alliin / PubChem CID 9576089"
  "C6H11NO3S"
  "substrate for alliinase"

allylSulfenicAcidSpecies : TK.Species
allylSulfenicAcidSpecies = literatureSpecies
  "allyl sulfenic acid"
  "C3H6OS"
  "short-lived intermediate in allicin formation"

allicinSpecies : TK.Species
allicinSpecies = literatureSpecies
  "allicin / PubChem CID 65036"
  "C6H10OS2"
  "reactive thiosulfinate"

pyruvateSpecies : TK.Species
pyruvateSpecies = literatureSpecies
  "pyruvate"
  "C3H3O3- / acid-base state context dependent"
  "alliinase coproduct"

ammoniaSpecies : TK.Species
ammoniaSpecies = literatureSpecies
  "ammonia/ammonium"
  "NH3/NH4+ depending on pH"
  "alliinase coproduct"

genericThiolSpecies : TK.Species
genericThiolSpecies = literatureSpecies
  "R-SH accessible biological thiol"
  "generic target family; composition target-specific"
  "GSH / bacillithiol / protein cysteine target"

sThioallylatedTargetSpecies : TK.Species
sThioallylatedTargetSpecies = literatureSpecies
  "R-S-allyl S-thioallylated target"
  "generic product family; composition target-specific"
  "modified low-molecular-weight or protein thiol"

alliinaseSpecies : TK.Species
alliinaseSpecies = literatureSpecies
  "alliinase EC 4.4.1.4"
  "protein catalyst; sequence/species specific"
  "PLP-dependent C-S lyase"

------------------------------------------------------------------------
-- Qualitative transition records. The alliinase entry intentionally does not
-- pretend one aggregate Transition is an atom-balanced elementary reaction;
-- it records the experimentally established pathway stage and leaves detailed
-- elementary stoichiometry to the molecular stoichiometric bridge.
------------------------------------------------------------------------

alliinaseStep : TK.Transition
alliinaseStep = record
  { transitionId = "alliinase cleavage: alliin -> allyl sulfenic acid + pyruvate + ammonia"
  ; transitionKind = TK.chemicalReaction
  ; reactants = TK.record { species = alliinSpecies ; coefficient = 1 } ∷ []
  ; products =
      TK.record { species = allylSulfenicAcidSpecies ; coefficient = 1 } ∷
      TK.record { species = pyruvateSpecies ; coefficient = 1 } ∷
      TK.record { species = ammoniaSpecies ; coefficient = 1 } ∷ []
  ; catalysts = alliinaseSpecies ∷ []
  ; rateLaw = TK.unknownRate
  ; condition = record
      { conditionLabel = "alliinase exposed to alliin after tissue disruption"
      ; environment = TK.emptyEnvironment
      ; guardExpression = "alliin and active alliinase/PLP share compartment"
      }
  ; reversibility = TK.irreversible
  ; evidence = TK.literatureEstablished
  }

sulfenicCondensation : TK.Transition
sulfenicCondensation = record
  { transitionId = "2 allyl sulfenic acid -> allicin + water (condensation representation)"
  ; transitionKind = TK.chemicalReaction
  ; reactants = TK.record { species = allylSulfenicAcidSpecies ; coefficient = 2 } ∷ []
  ; products = TK.record { species = allicinSpecies ; coefficient = 1 } ∷ []
  ; catalysts = []
  ; rateLaw = TK.unknownRate
  ; condition = record
      { conditionLabel = "spontaneous sulfenic-acid condensation"
      ; environment = TK.emptyEnvironment
      ; guardExpression = "allyl sulfenic acid co-present; solvent proton/water bookkeeping unresolved here"
      }
  ; reversibility = TK.irreversible
  ; evidence = TK.literatureEstablished
  }

allicinThiolTransition : TK.Transition
allicinThiolTransition = record
  { transitionId = "allicin-mediated S-thioallylation of accessible biological thiol"
  ; transitionKind = TK.chemicalReaction
  ; reactants =
      TK.record { species = allicinSpecies ; coefficient = 1 } ∷
      TK.record { species = genericThiolSpecies ; coefficient = 1 } ∷ []
  ; products = TK.record { species = sThioallylatedTargetSpecies ; coefficient = 1 } ∷ []
  ; catalysts = []
  ; rateLaw = TK.unknownRate
  ; condition = record
      { conditionLabel = "accessible nucleophilic thiol and allicin co-present"
      ; environment = TK.emptyEnvironment
      ; guardExpression = "target accessibility, protonation and competing thiols matter"
      }
  ; reversibility = TK.conditionallyReversible
  ; evidence = TK.literatureEstablished
  }

alliumCoreNetwork : TK.ReactionNetwork
alliumCoreNetwork = record
  { networkId = "Allium alliin -> allicin -> biological-thiol partial network"
  ; species =
      alliinSpecies ∷ allylSulfenicAcidSpecies ∷ allicinSpecies ∷
      pyruvateSpecies ∷ ammoniaSpecies ∷ genericThiolSpecies ∷
      sThioallylatedTargetSpecies ∷ alliinaseSpecies ∷ []
  ; transitions = alliinaseStep ∷ sulfenicCondensation ∷ allicinThiolTransition ∷ []
  ; compartments = []
  ; interfaces = []
  ; environment = TK.emptyEnvironment
  }

record AlliumNetworkBoundary : Set where
  constructor alliumNetworkBoundary
  field
    qualitativeNetworkIsExactKineticModel : Bool
    qualitativeNetworkIsExactKineticModelIsFalse :
      qualitativeNetworkIsExactKineticModel ≡ false

    pathwayMembershipProvesEyesalveDominance : Bool
    pathwayMembershipProvesEyesalveDominanceIsFalse :
      pathwayMembershipProvesEyesalveDominance ≡ false

    genericThiolTransitionIdentifiesEveryProteinTarget : Bool
    genericThiolTransitionIdentifiesEveryProteinTargetIsFalse :
      genericThiolTransitionIdentifiesEveryProteinTarget ≡ false

    sourceBackedPathwayCanSeedPreparationModel : Bool
    sourceBackedPathwayCanSeedPreparationModelIsTrue :
      sourceBackedPathwayCanSeedPreparationModel ≡ true

canonicalAlliumNetworkBoundary : AlliumNetworkBoundary
canonicalAlliumNetworkBoundary = alliumNetworkBoundary
  false refl false refl false refl true refl
