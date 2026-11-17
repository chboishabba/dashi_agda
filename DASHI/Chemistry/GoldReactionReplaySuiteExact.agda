module DASHI.Chemistry.GoldReactionReplaySuiteExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Chemistry.AtomicMolecularReactionLineageHyperfabricExact as Lineage
import DASHI.Chemistry.ElectronBondTransportExact as Electron
import DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact as Chlor
import DASHI.Biology.KitzerowBH4ReactionChemistryExact as BH4
import DASHI.Biology.KitzerowBH4SynthesisRegenerationExact as Cycle
import DASHI.Biology.IonicMimicryGeometryExact as Mimicry
import DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact as Carbon

------------------------------------------------------------------------
-- Five heterogeneous replay fixtures.  A gold replay is not a claim that every
-- microscopic coordinate is measured: it makes paid and unpaid coordinates
-- explicit over the common lineage hyperfabric.
------------------------------------------------------------------------

data ReplayClass : Set where
  electrochemicalHalfReaction : ReplayClass
  enzymeHydroxylation : ReplayClass
  cofactorRegeneration : ReplayClass
  ionicCoordinationSubstitution : ReplayClass
  carbonBondTransformation : ReplayClass

record GoldReactionReplay : Set where
  constructor goldReactionReplay
  field
    replayKey : String
    replayClass : ReplayClass
    canonicalSourceReference : String
    reactantProductReference : String
    atomMapReference : String
    electronOrRedoxReference : String
    bondChangeReference : String
    geometryReference : String
    environmentReference : String
    biologicalContextReference : String
    provenanceReference : String
    unpaidCoordinatesReference : String
    atomLineageExplicit : Bool
    electronAuditExplicit : Bool
    productsAndByproductsExplicit : Bool
    allKineticsMeasured : Bool
    completeMicroscopicMechanismProved : Bool

open GoldReactionReplay public

chlorAlkaliReplay : GoldReactionReplay
chlorAlkaliReplay = goldReactionReplay
  "gold-R1 chlor-alkali half-reaction"
  electrochemicalHalfReaction
  "DASHI.Chemistry.ChlorAlkaliCanonicalHalfReactionsExact"
  "canonical chlorine/hydrogen electrochemical half-reaction owners"
  "map chloride/chlorine or water/hydrogen nuclei through canonical stoichiometric half reaction"
  "explicit electron reservoir/equivalent bookkeeping from canonical half-reaction owner"
  "bond order/species change across electrode reaction"
  "electrode/interfacial geometry remains context-calibrated"
  "aqueous brine/electrode compartment"
  "industrial chemistry benchmark, not biological mechanism"
  "repo canonical chlor-alkali sources"
  "electrode potential/current-density/microkinetic pathway and interfacial density remain source-specific"
  true true true false false

pahReplay : GoldReactionReplay
pahReplay = goldReactionReplay
  "gold-R2 PAH BH4 hydroxylation"
  enzymeHydroxylation
  "DASHI.Biology.KitzerowBH4ReactionChemistryExact.pahReaction"
  "L-phenylalanine + O2 + BH4 -> L-tyrosine + qBH2 + H2O"
  "atom/isotope mapping required across phenylalanine oxygenation and pterin cycle"
  "BH4 oxidation/reducing-equivalent audit retained independently of atom balance"
  "C-H/O-H and aromatic hydroxylation bond-change coordinates"
  "PAH active-site geometry / Fe2+ context is independent calibration"
  "enzyme, pH, substrate, BH4, O2 and compartment context"
  "aromatic-amino-acid metabolism"
  "BH4 reaction source atlas"
  "site-specific atom map, kinetic constants and full catalytic intermediate sequence remain separately payable"
  true true true false false

dhprReplay : GoldReactionReplay
dhprReplay = goldReactionReplay
  "gold-R3 DHPR BH4 regeneration"
  cofactorRegeneration
  "DASHI.Biology.KitzerowBH4SynthesisRegenerationExact.dhprReaction"
  "BH2 + NADH + H+ -> BH4 + NAD+"
  "pterin and nicotinamide carrier lineage retained"
  "NADH hydride/electron-equivalent transfer explicitly represented"
  "pterin reduction changes electronic/bond-order state"
  "DHPR active-site geometry remains independently calibrated"
  "BH4 recycling compartment/redox context"
  "cofactor regeneration"
  "BH4 synthesis/regeneration source atlas"
  "quantitative redox potential, isotope atom map and kinetic parameters remain separately payable"
  true true true false false

pbCaReplay : GoldReactionReplay
pbCaReplay = goldReactionReplay
  "gold-R4 Pb/Ca coordination substitution"
  ionicCoordinationSubstitution
  "DASHI.Biology.IonicMimicryGeometryExact"
  "Pb2+ substitutes for Ca2+ at target-relative protein coordination sites in source-conditioned assays"
  "distinct Z=82 versus Z=20 atomic lineages are never collapsed"
  "no electron-transfer mechanism inferred merely from shared +2 formal charge"
  "coordination formation/loss and target-specific ligand geometry are first-class"
  "site rigidity, donor geometry and hydration determine local outcome"
  "source-specific Ca-binding protein environment"
  "protein recognition/function"
  "ionic mimicry source atlas"
  "site-specific affinities, occupancies, kinetics and downstream organism dose-response remain separately payable"
  true true true false false

carbonBondReplay : GoldReactionReplay
carbonBondReplay = goldReactionReplay
  "gold-R5 carbon-bond/prebiotic transformation"
  carbonBondTransformation
  "DASHI.Chemistry.CarbonChemicalSuitabilityLifeBoundaryExact + prebiotic reaction-network lane"
  "generic carbon-bearing condensation/hydrolysis transformation under explicit environment"
  "carbon and heteroatom lineage must be isotope/atom mapped per instantiated reaction"
  "redox/electron transfer is required only when the instantiated transformation is redox-active"
  "C-C/C-N/C-O bond formation or cleavage retained as explicit coordinate"
  "product geometry/stereo does not follow from formula alone"
  "solvent, temperature, pressure, pH, mineral/catalyst context"
  "prebiotic chemistry benchmark only"
  "carbon suitability and prebiotic source owners"
  "specific reaction identity, yield, kinetics, competing products and geochemical abundance remain experiment-specific"
  true true true false false

canonicalGoldReplays : List GoldReactionReplay
canonicalGoldReplays =
  chlorAlkaliReplay ∷ pahReplay ∷ dhprReplay ∷ pbCaReplay ∷ carbonBondReplay ∷ []

record GoldReactionReplaySuite : Set where
  constructor goldReactionReplaySuite
  field
    replays : List GoldReactionReplay
    replayCountAtLeastFive : Bool
    replayCountAtLeastFiveIsTrue : replayCountAtLeastFive ≡ true
    heterogeneousChemistryCovered : Bool
    heterogeneousChemistryCoveredIsTrue : heterogeneousChemistryCovered ≡ true
    everyReplayCompleteMicroscopicMechanism : Bool
    everyReplayCompleteMicroscopicMechanismIsFalse : everyReplayCompleteMicroscopicMechanism ≡ false

open GoldReactionReplaySuite public

canonicalGoldReactionReplaySuite : GoldReactionReplaySuite
canonicalGoldReactionReplaySuite =
  goldReactionReplaySuite canonicalGoldReplays true refl true refl false refl
