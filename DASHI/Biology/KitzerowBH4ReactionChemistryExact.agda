module DASHI.Biology.KitzerowBH4ReactionChemistryExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.TransitionKernel as Chemistry
import DASHI.Chemistry.AdmissibleReactionTransitionBridgeExact as Reaction
import DASHI.Physics.Chemistry.AtomicPeriodicTable369ChemistryHyperfibreBridgeExact as AtomicChem

------------------------------------------------------------------------
-- Reaction-level BH4 chemistry.
--
-- The biological cascade owner uses pathway/node labels.  This owner descends
-- those labels into repo-native Species / StoichiometricTerm / Transition
-- objects.  It reuses the existing atomic->molecular->reaction hyperfibre and
-- keeps quantitative kinetics, exact element balance and wet-lab promotion
-- fail-closed unless separately paid.
------------------------------------------------------------------------

mkSpecies : String -> String -> Chemistry.Species
mkSpecies ident composition = record
  { speciesId = ident
  ; phase = Chemistry.dissolved
  ; chargeLabel = "physiological protonation / charge state context-dependent"
  ; compositionLabel = composition
  ; mobilityClass = Chemistry.mobile
  ; activityModelLabel = "biochemical aqueous activity; quantitative activity model unpaid"
  ; opticalRoleLabel = "none asserted"
  ; evidence = Chemistry.literatureEstablished
  }

term : Chemistry.Species -> Nat -> Chemistry.StoichiometricTerm
term s n = record { species = s ; coefficient = n }

biochemicalCondition : String -> Chemistry.Condition
biochemicalCondition label = record
  { conditionLabel = label
  ; environment = Chemistry.emptyEnvironment
  ; guardExpression = "enzyme/cofactor/substrate/compartment availability required; quantitative pH, temperature and ionic-strength calibration unpaid"
  }

mmRate : String -> Chemistry.RateLaw
mmRate reference = record
  { rateLawKind = Chemistry.michaelisMenten
  ; symbolicForm = "Michaelis-Menten family; parameter values intentionally not fabricated"
  ; parameters = []
  ; validityRegime = reference
  ; evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- Molecular species.
------------------------------------------------------------------------

gtp h2o formate dhnTriphosphate bh4 qbh2 oxygen : Chemistry.Species
gtp = mkSpecies "GTP" "guanosine 5'-triphosphate"
h2o = mkSpecies "H2O" "water"
formate = mkSpecies "formate" "methanoate / formate"
dhnTriphosphate = mkSpecies "7,8-dihydroneopterin-3'-triphosphate" "GCH1 product; exact molecular identity retained by source reference"
bh4 = mkSpecies "6R-BH4" "(6R)-5,6,7,8-tetrahydrobiopterin"
qbh2 = mkSpecies "qBH2" "quinonoid dihydrobiopterin / BH4 hydroxylase-cycle oxidation product"
oxygen = mkSpecies "O2" "molecular oxygen"

phe tyr trp fiveHTP dopa : Chemistry.Species
phe = mkSpecies "L-phenylalanine" "C9H11NO2"
tyr = mkSpecies "L-tyrosine" "C9H11NO3"
trp = mkSpecies "L-tryptophan" "C11H12N2O2"
fiveHTP = mkSpecies "5-hydroxy-L-tryptophan" "C11H12N2O3"
dopa = mkSpecies "L-DOPA" "C9H11NO4"

arginine citrulline nitricOxide superoxide nadph nadp : Chemistry.Species
arginine = mkSpecies "L-arginine" "C6H14N4O2"
citrulline = mkSpecies "L-citrulline" "C6H13N3O3"
nitricOxide = mkSpecies "NO" "nitric oxide"
superoxide = mkSpecies "O2.-" "superoxide radical anion"
nadph = mkSpecies "NADPH" "reduced nicotinamide adenine dinucleotide phosphate"
nadp = mkSpecies "NADP+" "oxidized nicotinamide adenine dinucleotide phosphate"

alkylglycerol glycerolDerivative fattyAldehyde bh2 : Chemistry.Species
alkylglycerol = mkSpecies "lyso-alkylglycerol/ether-lipid substrate" "parameterised alkylglycerol species family; R-chain identity must be supplied per assay"
glycerolDerivative = mkSpecies "AGMO glycerol derivative" "product family determined by ether-lipid headgroup"
fattyAldehyde = mkSpecies "fatty aldehyde" "R-CHO product family from ether-bond cleavage"
bh2 = mkSpecies "6,7-dihydrobiopterin" "AGMO pterin oxidation product"

------------------------------------------------------------------------
-- Enzyme/cofactor species.  They are explicit catalysts, not hidden in labels.
------------------------------------------------------------------------

gch1 pah th tph nos fad fmn heme agmo : Chemistry.Species
gch1 = mkSpecies "GCH1" "GTP cyclohydrolase I enzyme; EC 3.5.4.16"
pah = mkSpecies "PAH" "phenylalanine hydroxylase; EC 1.14.16.1"
th = mkSpecies "TH" "tyrosine hydroxylase; EC 1.14.16.2"
tph = mkSpecies "TPH" "tryptophan hydroxylase; EC 1.14.16.4"
nos = mkSpecies "NOS" "nitric-oxide synthase isoform context required"
fad = mkSpecies "FAD" "flavin adenine dinucleotide"
fmn = mkSpecies "FMN" "flavin mononucleotide"
heme = mkSpecies "heme" "NOS heme cofactor"
agmo = mkSpecies "AGMO" "alkylglycerol monooxygenase; EC 1.14.16.5"

------------------------------------------------------------------------
-- GCH1: GTP + H2O -> formate + 7,8-dihydroneopterin triphosphate.
------------------------------------------------------------------------

gch1Reaction : Chemistry.Transition
gch1Reaction = record
  { transitionId = "BH4-R1 GCH1 de-novo entry"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term gtp 1 ∷ term h2o 1 ∷ []
  ; products = term formate 1 ∷ term dhnTriphosphate 1 ∷ []
  ; catalysts = gch1 ∷ []
  ; rateLaw = mmRate "BRENDA EC 3.5.4.16; human GCH1 P30793"
  ; condition = biochemicalCondition "cytosolic GCH1 de-novo BH4 synthesis entry"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- Aromatic amino-acid hydroxylases.
-- Net cofactor-cycle representation:
-- amino acid + O2 + BH4 -> hydroxylated amino acid + qBH2 + H2O.
------------------------------------------------------------------------

pahReaction thReaction tphReaction : Chemistry.Transition
pahReaction = record
  { transitionId = "BH4-R2 PAH phenylalanine hydroxylation"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term phe 1 ∷ term oxygen 1 ∷ term bh4 1 ∷ []
  ; products = term tyr 1 ∷ term qbh2 1 ∷ term h2o 1 ∷ []
  ; catalysts = pah ∷ []
  ; rateLaw = mmRate "PAH BH4-dependent aromatic amino-acid hydroxylase"
  ; condition = biochemicalCondition "PAH / non-heme Fe2+ / BH4 context"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

thReaction = record
  { transitionId = "BH4-R3 TH tyrosine hydroxylation"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term tyr 1 ∷ term oxygen 1 ∷ term bh4 1 ∷ []
  ; products = term dopa 1 ∷ term qbh2 1 ∷ term h2o 1 ∷ []
  ; catalysts = th ∷ []
  ; rateLaw = mmRate "TH BH4-dependent aromatic amino-acid hydroxylase"
  ; condition = biochemicalCondition "TH / non-heme Fe2+ / BH4 context"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

tphReaction = record
  { transitionId = "BH4-R4 TPH tryptophan hydroxylation"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term trp 1 ∷ term oxygen 1 ∷ term bh4 1 ∷ []
  ; products = term fiveHTP 1 ∷ term qbh2 1 ∷ term h2o 1 ∷ []
  ; catalysts = tph ∷ []
  ; rateLaw = mmRate "TPH BH4-dependent aromatic amino-acid hydroxylase"
  ; condition = biochemicalCondition "TPH / non-heme Fe2+ / BH4 context"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- NOS coupled and uncoupled branches.
-- Coupled stoichiometry uses the literature electron/substrate accounting
-- multiplied by two to avoid fractional Nat coefficients:
-- 2 Arg + 4 O2 + 3 NADPH -> 2 Cit + 2 NO + 3 NADP+.
-- BH4/FAD/FMN/heme are carried explicitly as catalytic context.
------------------------------------------------------------------------

nosCoupledReaction nosUncoupledReaction : Chemistry.Transition
nosCoupledReaction = record
  { transitionId = "BH4-R5 coupled NOS nitric-oxide production"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term arginine 2 ∷ term oxygen 4 ∷ term nadph 3 ∷ []
  ; products = term citrulline 2 ∷ term nitricOxide 2 ∷ term nadp 3 ∷ []
  ; catalysts = nos ∷ bh4 ∷ fad ∷ fmn ∷ heme ∷ []
  ; rateLaw = mmRate "NOS two-step oxidation; 1.5 NADPH and 2 O2 per citrulline/NO pair"
  ; condition = biochemicalCondition "coupled NOS: adequate BH4/substrate, dimer and isoform-specific CaM context"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

nosUncoupledReaction = record
  { transitionId = "BH4-R6 NOS uncoupled superoxide branch"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term oxygen 1 ∷ term nadph 1 ∷ []
  ; products = term superoxide 1 ∷ term nadp 1 ∷ []
  ; catalysts = nos ∷ fad ∷ fmn ∷ heme ∷ []
  ; rateLaw = mmRate "qualitative uncoupled NOS electron leakage; exact proton/electron balance remains a quantitative obligation"
  ; condition = biochemicalCondition "BH4/substrate/dimer insufficiency can favour superoxide rather than NO"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

------------------------------------------------------------------------
-- AGMO ether-lipid cleavage.  The substrate and product are deliberately
-- parameterised species families because the R-chain/headgroup must be pinned
-- per assay.  Literature supports approximately 1:1 pterin oxidation to ether
-- lipid cleavage.
------------------------------------------------------------------------

agmoReaction : Chemistry.Transition
agmoReaction = record
  { transitionId = "BH4-R7 AGMO ether-lipid cleavage"
  ; transitionKind = Chemistry.chemicalReaction
  ; reactants = term alkylglycerol 1 ∷ term oxygen 1 ∷ term bh4 1 ∷ []
  ; products = term glycerolDerivative 1 ∷ term fattyAldehyde 1 ∷ term bh2 1 ∷ []
  ; catalysts = agmo ∷ []
  ; rateLaw = mmRate "AGMO EC 1.14.16.5; BH4-dependent mixed-function oxygenase"
  ; condition = biochemicalCondition "membrane-associated AGMO; exact ether-lipid molecular species and assay context required"
  ; reversibility = Chemistry.irreversible
  ; evidence = Chemistry.literatureEstablished
  }

canonicalBH4ReactionNetwork : Chemistry.ReactionNetwork
canonicalBH4ReactionNetwork = record
  { networkId = "Kitzerow-facing BH4 literal biochemical reaction network"
  ; species =
      gtp ∷ h2o ∷ formate ∷ dhnTriphosphate ∷ bh4 ∷ qbh2 ∷ bh2 ∷ oxygen
      ∷ phe ∷ tyr ∷ trp ∷ fiveHTP ∷ dopa
      ∷ arginine ∷ citrulline ∷ nitricOxide ∷ superoxide ∷ nadph ∷ nadp
      ∷ alkylglycerol ∷ glycerolDerivative ∷ fattyAldehyde
      ∷ gch1 ∷ pah ∷ th ∷ tph ∷ nos ∷ fad ∷ fmn ∷ heme ∷ agmo ∷ []
  ; transitions =
      gch1Reaction ∷ pahReaction ∷ thReaction ∷ tphReaction
      ∷ nosCoupledReaction ∷ nosUncoupledReaction ∷ agmoReaction ∷ []
  ; compartments = []
  ; interfaces = []
  ; environment = Chemistry.emptyEnvironment
  }

------------------------------------------------------------------------
-- Cross-scale receipt: the literal network consumes the already-existing
-- atomic->molecular->reaction chemistry programme, but does not claim that the
-- 369 periodic construction determines molecular geometry or reaction path.
------------------------------------------------------------------------

atomicChemistryBoundary : AtomicChem.AtomicChemistryCrossPollinationBoundary
atomicChemistryBoundary = AtomicChem.canonicalAtomicChemistryCrossPollinationBoundary

reactionMDLBoundary : Reaction.ReactionMDLBoundary
reactionMDLBoundary = Reaction.canonicalReactionMDLBoundary

record BH4ReactionChemistryBoundary : Set where
  constructor bh4ReactionChemistryBoundary
  field
    pathwayLabelAloneCountsAsReaction : Bool
    pathwayLabelAloneCountsAsReactionIsFalse : pathwayLabelAloneCountsAsReaction ≡ false
    speciesAndStoichiometryExplicit : Bool
    speciesAndStoichiometryExplicitIsTrue : speciesAndStoichiometryExplicit ≡ true
    atomic369DeterminesReactionPath : Bool
    atomic369DeterminesReactionPathIsFalse : atomic369DeterminesReactionPath ≡ false
    quantitativeKineticsPromoted : Bool
    quantitativeKineticsPromotedIsFalse : quantitativeKineticsPromoted ≡ false
    exactElementChargeBalancePromotedForEveryTransition : Bool
    exactElementChargeBalancePromotedForEveryTransitionIsFalse : exactElementChargeBalancePromotedForEveryTransition ≡ false
    wetLabValidationPromoted : Bool
    wetLabValidationPromotedIsFalse : wetLabValidationPromoted ≡ false

canonicalBH4ReactionChemistryBoundary : BH4ReactionChemistryBoundary
canonicalBH4ReactionChemistryBoundary =
  bh4ReactionChemistryBoundary false refl true refl false refl false refl false refl false refl
