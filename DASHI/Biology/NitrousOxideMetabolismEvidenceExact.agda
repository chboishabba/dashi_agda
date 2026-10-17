module DASHI.Biology.NitrousOxideMetabolismEvidenceExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Source
import DASHI.Core.GenericReceipt as Receipt
import DASHI.Biology.NitrogenOxideSpeciesCouplingExact as Oxide

------------------------------------------------------------------------
-- NITROUS OXIDE / NANG METABOLIC EVIDENCE LANE
--
-- Bounded literature-backed lane for N2O.  The acquired evidence supports
-- functional cobalamin inactivation and methionine-synthase disruption under
-- clinically relevant exposure.  It does not identify N2O with nitric oxide,
-- NOS catalysis, BH4 depletion, or the Kitzerow allocator mechanism.
------------------------------------------------------------------------

cmajNitrousOxideReview2023 : Source.AttributedSource
cmajNitrousOxideReview2023 =
  Source.mkDOISource
    "Cyrille De Halleux; David N. Juurlink"
    "Diagnosis and management of toxicity associated with the recreational use of nitrous oxide"
    "CMAJ 195(32):E1075-E1081"
    "2023"
    "10.1503/cmaj.230196"
    "https://pubmed.ncbi.nlm.nih.gov/37604519/"
    Source.academicArticleSource
    "bounded review evidence for N2O functional vitamin-B12 deficiency, cobalamin oxidation and methionine-synthase inhibition"
    Source.publicAttribution

data N2OMetabolicTarget : Set where
  cobalaminCobaltState : N2OMetabolicTarget
  methionineSynthaseActivity : N2OMetabolicTarget
  homocysteineState : N2OMetabolicTarget
  methionineState : N2OMetabolicTarget
  folateCycleState : N2OMetabolicTarget
  neurologicalOutcome : N2OMetabolicTarget

record NitrousOxideEvidenceReceipt : Set where
  constructor nitrous-oxide-evidence-receipt
  field
    receiptId : String
    source : Source.AttributedSource
    species : Oxide.NitrogenOxideSpecies
    target : N2OMetabolicTarget
    boundedReading : String
    evidenceReference : String
    directBH4Measurement : Bool
    directNOSCouplingMeasurement : Bool
    createsKitzerowWholeModelProof : Bool
    createsKitzerowWholeModelProofIsFalse :
      createsKitzerowWholeModelProof ≡ false

open NitrousOxideEvidenceReceipt public

cobalaminOxidationReceipt : NitrousOxideEvidenceReceipt
cobalaminOxidationReceipt =
  nitrous-oxide-evidence-receipt
    "N2O-E1"
    cmajNitrousOxideReview2023
    Oxide.nitrousOxide
    cobalaminCobaltState
    "Nitrous oxide can produce functional vitamin-B12 deficiency through oxidation/inactivation of cobalamin chemistry."
    "CMAJ 2023 review; DOI 10.1503/cmaj.230196; PMID 37604519"
    false false false refl

methionineSynthaseReceipt : NitrousOxideEvidenceReceipt
methionineSynthaseReceipt =
  nitrous-oxide-evidence-receipt
    "N2O-E2"
    cmajNitrousOxideReview2023
    Oxide.nitrousOxide
    methionineSynthaseActivity
    "N2O-mediated functional cobalamin deficiency inhibits methionine synthase, with downstream homocysteine/methionine/folate consequences."
    "CMAJ 2023 review; DOI 10.1503/cmaj.230196; PMID 37604519"
    false false false refl

record NitrousOxideMetabolismBoundary : Set where
  constructor nitrous-oxide-metabolism-boundary
  field
    nitrousOxideEvidenceCreatesNitricOxideIdentity : Bool
    nitrousOxideEvidenceCreatesNitricOxideIdentityIsFalse :
      nitrousOxideEvidenceCreatesNitricOxideIdentity ≡ false
    nitrousOxideEvidenceCreatesNOSUncouplingProof : Bool
    nitrousOxideEvidenceCreatesNOSUncouplingProofIsFalse :
      nitrousOxideEvidenceCreatesNOSUncouplingProof ≡ false
    cobalaminOxidationEstablishesBH4Depletion : Bool
    cobalaminOxidationEstablishesBH4DepletionIsFalse :
      cobalaminOxidationEstablishesBH4Depletion ≡ false
    methionineSynthaseInhibitionEstablishesAutismMechanism : Bool
    methionineSynthaseInhibitionEstablishesAutismMechanismIsFalse :
      methionineSynthaseInhibitionEstablishesAutismMechanism ≡ false

canonicalNitrousOxideMetabolismBoundary : NitrousOxideMetabolismBoundary
canonicalNitrousOxideMetabolismBoundary =
  nitrous-oxide-metabolism-boundary false refl false refl false refl false refl

canonicalNitrousOxideMetabolismReceipt : Receipt.GenericReceipt
canonicalNitrousOxideMetabolismReceipt =
  Receipt.mkNonPromotingReceipt
    "nitrous oxide metabolic evidence"
    "DASHI.Biology.NitrousOxideMetabolismEvidenceExact"
    "N2O -> cobalamin / methionine-synthase bounded evidence lane"
    "records literature-backed N2O metabolic effects without collapsing them into NO/NOS/BH4 chemistry"
    "N2O evidence does not create NO identity, NOS uncoupling, BH4 depletion or autism-mechanism proof"
    "agda -i . DASHI/Biology/NitrousOxideMetabolismEvidenceExact.agda"
