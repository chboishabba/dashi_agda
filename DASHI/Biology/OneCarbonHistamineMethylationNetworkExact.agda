module DASHI.Biology.OneCarbonHistamineMethylationNetworkExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Biology.ChegenWalshUndermethylationSourceAtlasExact as Sources

------------------------------------------------------------------------
-- ONE-CARBON / SAM / HISTAMINE NETWORK
--
-- This owner encodes source-bounded biochemical edges needed to evaluate the
-- reel's "one biochemical route" claim.  Shared use of SAM is represented as
-- a common-resource relation, not pathway identity.
------------------------------------------------------------------------

data Molecule : Set where
  methyleneTHF : Molecule
  methylTHF : Molecule
  homocysteine : Molecule
  methionine : Molecule
  sam : Molecule
  sah : Molecule
  histamine : Molecule
  methylhistamine : Molecule
  catecholamineSubstrate : Molecule
  methylatedCatecholamineProduct : Molecule
  genomicSubstrate : Molecule
  methylatedGenomicProduct : Molecule

data Enzyme : Set where
  mthfr : Enzyme
  methionineSynthase : Enzyme
  methionineAdenosyltransferase : Enzyme
  hnmt : Enzyme
  comt : Enzyme
  dnmt : Enzyme

data ProcessClass : Set where
  folateCycle : ProcessClass
  methionineCycle : ProcessClass
  histamineInactivation : ProcessClass
  catecholMetabolism : ProcessClass
  epigeneticMethylation : ProcessClass

data EdgeSupport : Set where
  literatureEstablished : EdgeSupport
  sourceReported : EdgeSupport
  dashiCandidate : EdgeSupport

record BiochemicalEdge : Set where
  constructor biochemicalEdge
  field
    substrate : Molecule
    product : Molecule
    catalyst : Enzyme
    process : ProcessClass
    support : EdgeSupport
    source : Source.AttributedSource
    sourceReading : String

open BiochemicalEdge public

mthfrEdge : BiochemicalEdge
mthfrEdge =
  biochemicalEdge
    methyleneTHF methylTHF mthfr folateCycle literatureEstablished
    Sources.mthfrPerspective2026
    "MTHFR reduces 5,10-methylene-THF to 5-methyl-THF, directing one-carbon units toward the methionine cycle."

methionineToSAMEdge : BiochemicalEdge
methionineToSAMEdge =
  biochemicalEdge
    methionine sam methionineAdenosyltransferase methionineCycle
    literatureEstablished Sources.mthfrPerspective2026
    "The methionine cycle supplies SAM, a principal cellular methyl donor."

hnmtHistamineEdge : BiochemicalEdge
hnmtHistamineEdge =
  biochemicalEdge
    histamine methylhistamine hnmt histamineInactivation
    literatureEstablished Sources.samMethyltransferases2021
    "HNMT is a SAM-dependent methyltransferase that methylates histamine."

comtCatecholEdge : BiochemicalEdge
comtCatecholEdge =
  biochemicalEdge
    catecholamineSubstrate methylatedCatecholamineProduct comt
    catecholMetabolism literatureEstablished
    Sources.samMethyltransferases2021
    "COMT is a SAM-dependent methyltransferase acting on catechol substrates; this is metabolism/clearance chemistry and is not identical to neurotransmitter biosynthesis."

dnmtGenomicEdge : BiochemicalEdge
dnmtGenomicEdge =
  biochemicalEdge
    genomicSubstrate methylatedGenomicProduct dnmt
    epigeneticMethylation literatureEstablished
    Sources.samMethyltransferases2021
    "DNMT enzymes use SAM for genomic methylation; sharing SAM with HNMT/COMT does not make the processes one pathway."

canonicalBiochemicalEdges : List BiochemicalEdge
canonicalBiochemicalEdges =
  mthfrEdge
  ∷ methionineToSAMEdge
  ∷ hnmtHistamineEdge
  ∷ comtCatecholEdge
  ∷ dnmtGenomicEdge
  ∷ []

------------------------------------------------------------------------
-- Distinct-state / distinct-pathway firewalls.
------------------------------------------------------------------------

data SharedSAMDependencyImpliesSamePathway : Set where
data HistamineMethylationEqualsEpigeneticMethylation : Set where
data COMTMetabolismEqualsNeurotransmitterSynthesis : Set where
data MTHFRVariantEqualsGlobalMethylationState : Set where
data OneCarbonStateEqualsPersonalityPhenotype : Set where

sharedSAMDoesNotIdentifySamePathway :
  SharedSAMDependencyImpliesSamePathway → ⊥
sharedSAMDoesNotIdentifySamePathway ()

histamineMethylationNotEpigeneticIdentity :
  HistamineMethylationEqualsEpigeneticMethylation → ⊥
histamineMethylationNotEpigeneticIdentity ()

comtMetabolismNotBiosynthesisIdentity :
  COMTMetabolismEqualsNeurotransmitterSynthesis → ⊥
comtMetabolismNotBiosynthesisIdentity ()

mthfrVariantDoesNotDefineGlobalMethylationState :
  MTHFRVariantEqualsGlobalMethylationState → ⊥
mthfrVariantDoesNotDefineGlobalMethylationState ()

oneCarbonStateDoesNotDefinePersonalityPhenotype :
  OneCarbonStateEqualsPersonalityPhenotype → ⊥
oneCarbonStateDoesNotDefinePersonalityPhenotype ()

------------------------------------------------------------------------
-- "Undermethylation" is not one primitive biochemical variable.
------------------------------------------------------------------------

data MethylationStateClaim : Set where
  lowSAMRelativeToSAH : MethylationStateClaim
  reducedSpecificMethyltransferaseFlux : Enzyme → MethylationStateClaim
  reducedGenomicMethylation : MethylationStateClaim
  inheritedSevereMTHFRDeficiency : MethylationStateClaim
  commonMTHFRVariantCarrier : MethylationStateClaim
  walshUndermethylationLabel : MethylationStateClaim

data LowSAMSAHEqualsWalshLabel : Set where
data HNMTFluxEqualsWalshLabel : Set where
data GenomicHypomethylationEqualsWalshLabel : Set where
data MTHFRCarrierEqualsWalshLabel : Set where

lowSAMSAHDoesNotDefinitionallyEqualWalshLabel :
  LowSAMSAHEqualsWalshLabel → ⊥
lowSAMSAHDoesNotDefinitionallyEqualWalshLabel ()

hnmtFluxDoesNotDefinitionallyEqualWalshLabel :
  HNMTFluxEqualsWalshLabel → ⊥
hnmtFluxDoesNotDefinitionallyEqualWalshLabel ()

genomicHypomethylationDoesNotDefinitionallyEqualWalshLabel :
  GenomicHypomethylationEqualsWalshLabel → ⊥
genomicHypomethylationDoesNotDefinitionallyEqualWalshLabel ()

mthfrCarrierDoesNotDefinitionallyEqualWalshLabel :
  MTHFRCarrierEqualsWalshLabel → ⊥
mthfrCarrierDoesNotDefinitionallyEqualWalshLabel ()
