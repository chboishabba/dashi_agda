module DASHI.Biology.BH4MissingReactionKineticsEvidenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.GenericReceipt as Receipt

data MissingReactionKineticsTarget : Set where
  PCBD1-RHEA11920 : MissingReactionKineticsTarget
  NOS-RHEA19897 : MissingReactionKineticsTarget

record PrimaryKineticsEvidence : Set where
  constructor primary-kinetics-evidence
  field
    target : MissingReactionKineticsTarget
    sourceReference : String
    primaryHumanEvidence : Bool
    quantitativeKineticsReported : Bool
    exactNetworkFluxBoundPaid : Bool

open PrimaryKineticsEvidence public

pcbd1Johnen1995 : PrimaryKineticsEvidence
pcbd1Johnen1995 =
  primary-kinetics-evidence
    PCBD1-RHEA11920
    "Johnen et al., PNAS 1995, DOI:10.1073/pnas.92.26.12384; human 4a-carbinolamine dehydratase; non-Michaelis-Menten kinetics, Hill coefficient 1.8; mutant C82R Km approximately 5 uM with 60% lower Vmax"
    true true false

pcbd1Thony1995 : PrimaryKineticsEvidence
pcbd1Thony1995 =
  primary-kinetics-evidence
    PCBD1-RHEA11920
    "Thony et al., Eur J Biochem 1995, DOI:10.1111/j.1432-1033.1995.tb20714.x; purified human wild-type PCBD1/dehydratase; approximately 50-70-fold acceleration of synthetic substrate dehydration"
    true true false

nos2Human1997 : PrimaryKineticsEvidence
nos2Human1997 =
  primary-kinetics-evidence
    NOS-RHEA19897
    "PMID:9224737; recombinant human inducible NOS; Vmax approximately 800 nmol NO min^-1 mg^-1 and Km(L-Arg) 22 uM with BH4 required during purification"
    true true false

nos3Placenta1997 : PrimaryKineticsEvidence
nos3Placenta1997 =
  primary-kinetics-evidence
    NOS-RHEA19897
    "PMID:9089781; human placental NOS3; apparent Km(L-Arg) 3.12+/-1.99 uM without added BH4 and 2.06+/-1.13 uM with 50 uM BH4; Vmax 2.5-7.55 versus 13.3-58.5 pmol min^-1 mg^-1; half-maximal BH4 response near 79 nM"
    true true false

record MissingReactionKineticsBoundary : Set where
  constructor missing-reaction-kinetics-boundary
  field
    primaryKineticsCreatesNetworkFluxBound : Bool
    primaryKineticsCreatesNetworkFluxBoundIsFalse : primaryKineticsCreatesNetworkFluxBound ≡ false
    isoformSpecificNOSKineticsCreatesSharedNOSFlux : Bool
    isoformSpecificNOSKineticsCreatesSharedNOSFluxIsFalse : isoformSpecificNOSKineticsCreatesSharedNOSFlux ≡ false
    mutantPCBD1KineticsCreatesWildTypeFlux : Bool
    mutantPCBD1KineticsCreatesWildTypeFluxIsFalse : mutantPCBD1KineticsCreatesWildTypeFlux ≡ false
    assayVmaxCreatesInVivoCompartmentFlux : Bool
    assayVmaxCreatesInVivoCompartmentFluxIsFalse : assayVmaxCreatesInVivoCompartmentFlux ≡ false

open MissingReactionKineticsBoundary public

canonicalMissingReactionKineticsBoundary : MissingReactionKineticsBoundary
canonicalMissingReactionKineticsBoundary =
  missing-reaction-kinetics-boundary false refl false refl false refl false refl

canonicalMissingReactionKineticsReceipt : Receipt.GenericReceipt
canonicalMissingReactionKineticsReceipt =
  Receipt.mkNonPromotingReceipt
    "primary kinetics evidence for SABIO-uncovered BH4 reactions"
    "DASHI.Biology.BH4MissingReactionKineticsEvidenceExact"
    "RHEA:11920 PCBD1 and RHEA:19897 NOS are not evidence-free: primary human biochemical studies report quantitative kinetic behavior for PCBD1 and human NOS isoforms"
    "fills the literature-discovery gap left by exact-UniProt SABIO coverage while preserving assay/isoform/compartment distinctions"
    "primary assay kinetics are not network flux bounds; NOS isoform kinetics cannot be silently collapsed into one shared in-vivo RHEA:19897 flux; mutant PCBD1 kinetics do not substitute for wild-type cellular flux"
    "primary literature receipt only; quantitative adjudication remains open"
