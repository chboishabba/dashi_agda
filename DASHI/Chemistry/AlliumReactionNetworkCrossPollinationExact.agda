module DASHI.Chemistry.AlliumReactionNetworkCrossPollinationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat; _+_)
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
--   alliinase: alliin + H2O -> allyl sulfenic acid + pyruvic acid + NH3;
--   two allyl sulfenic-acid molecules then condense nonenzymatically to
--   allicin + H2O.
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

waterSpecies : TK.Species
waterSpecies = literatureSpecies
  "water"
  "H2O"
  "reaction/solvent participant"

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

pyruvicAcidSpecies : TK.Species
pyruvicAcidSpecies = literatureSpecies
  "pyruvic acid / pyruvate acid-base family"
  "C3H4O3 neutral bookkeeping form"
  "alliinase coproduct"

ammoniaSpecies : TK.Species
ammoniaSpecies = literatureSpecies
  "ammonia / ammonium acid-base family"
  "NH3 neutral bookkeeping form"
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
-- Exact finite atom-count checks for the two resolved small-molecule pathway
-- stages.  These are arithmetic checks of the neutral bookkeeping equations,
-- not kinetic or mechanistic completeness claims.
------------------------------------------------------------------------

record CHNOSBalance : Set where
  constructor chnosBalance
  field
    cLeft cRight : Nat
    hLeft hRight : Nat
    nLeft nRight : Nat
    oLeft oRight : Nat
    sLeft sRight : Nat
    carbonBalanced : cLeft ≡ cRight
    hydrogenBalanced : hLeft ≡ hRight
    nitrogenBalanced : nLeft ≡ nRight
    oxygenBalanced : oLeft ≡ oRight
    sulfurBalanced : sLeft ≡ sRight

alliinaseNeutralBalance : CHNOSBalance
alliinaseNeutralBalance = chnosBalance
  6 6
  (11 + 2) (6 + 4 + 3)
  1 1
  (3 + 1) (1 + 3)
  1 1
  refl refl refl refl refl

sulfenicCondensationBalance : CHNOSBalance
sulfenicCondensationBalance = chnosBalance
  (3 + 3) 6
  (6 + 6) (10 + 2)
  0 0
  (1 + 1) (1 + 1)
  (1 + 1) 2
  refl refl refl refl refl

------------------------------------------------------------------------
-- Qualitative transition records.  The two biosynthetic stages above now have
-- atom-count receipts.  The generic thiol transition remains family-level
-- because R-SH denotes many chemically distinct biological targets.
------------------------------------------------------------------------

alliinaseStep : TK.Transition
alliinaseStep = record
  { transitionId = "alliinase cleavage: alliin + H2O -> allyl sulfenic acid + pyruvic acid + NH3"
  ; transitionKind = TK.chemicalReaction
  ; reactants =
      record { species = alliinSpecies ; coefficient = 1 } ∷
      record { species = waterSpecies ; coefficient = 1 } ∷ []
  ; products =
      record { species = allylSulfenicAcidSpecies ; coefficient = 1 } ∷
      record { species = pyruvicAcidSpecies ; coefficient = 1 } ∷
      record { species = ammoniaSpecies ; coefficient = 1 } ∷ []
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
  { transitionId = "2 allyl sulfenic acid -> allicin + H2O"
  ; transitionKind = TK.chemicalReaction
  ; reactants = record { species = allylSulfenicAcidSpecies ; coefficient = 2 } ∷ []
  ; products =
      record { species = allicinSpecies ; coefficient = 1 } ∷
      record { species = waterSpecies ; coefficient = 1 } ∷ []
  ; catalysts = []
  ; rateLaw = TK.unknownRate
  ; condition = record
      { conditionLabel = "spontaneous sulfenic-acid condensation"
      ; environment = TK.emptyEnvironment
      ; guardExpression = "two allyl sulfenic-acid equivalents co-present"
      }
  ; reversibility = TK.irreversible
  ; evidence = TK.literatureEstablished
  }

allicinThiolTransition : TK.Transition
allicinThiolTransition = record
  { transitionId = "allicin-mediated S-thioallylation of accessible biological thiol"
  ; transitionKind = TK.chemicalReaction
  ; reactants =
      record { species = allicinSpecies ; coefficient = 1 } ∷
      record { species = genericThiolSpecies ; coefficient = 1 } ∷ []
  ; products = record { species = sThioallylatedTargetSpecies ; coefficient = 1 } ∷ []
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
      alliinSpecies ∷ waterSpecies ∷ allylSulfenicAcidSpecies ∷ allicinSpecies ∷
      pyruvicAcidSpecies ∷ ammoniaSpecies ∷ genericThiolSpecies ∷
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

    atomBalanceProvesUniqueElementaryMechanism : Bool
    atomBalanceProvesUniqueElementaryMechanismIsFalse :
      atomBalanceProvesUniqueElementaryMechanism ≡ false

    sourceBackedPathwayCanSeedPreparationModel : Bool
    sourceBackedPathwayCanSeedPreparationModelIsTrue :
      sourceBackedPathwayCanSeedPreparationModel ≡ true

canonicalAlliumNetworkBoundary : AlliumNetworkBoundary
canonicalAlliumNetworkBoundary = alliumNetworkBoundary
  false refl false refl false refl false refl true refl
