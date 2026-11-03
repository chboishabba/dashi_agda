module DASHI.Biology.Wong2022ScientificMetabolicBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.ScientificMechanismEvidenceBidiExact as Science
import DASHI.Biology.Wong2022LysergicAcidEvidenceExact as Wong
import DASHI.Biology.Wong2022EvidenceLedgerExact as Ledger
import DASHI.Biology.Wong2022LysergicAcidFiniteCore as Core
import DASHI.Biology.Cell.OpenMetabolicNetwork as Metabolic
import DASHI.Biology.Cell.MetabolicStoichiometricConservation as Stoich

------------------------------------------------------------------------
-- WONG 2022 SCIENTIFIC / STOICHIOMETRIC CROSS-OWNER BRIDGE
--
-- Credit experimental source: Wong, Lim, Tan, Go, Bell, Freemont, Yew.
-- Nature Communications 13:712 (2022).
-- DOI 10.1038/s41467-022-28386-6.
--
-- Import existing scientific-evidence and metabolic-conservation theorem
-- owners. Do not create a parallel empirical, ontology or chemistry engine.
------------------------------------------------------------------------

productionObservation : Science.ScientificMechanismReceipt
productionObservation =
  Science.scientific-mechanism-receipt
    "Wong 2022 engineered yeast"
    "Authors report D-lysergic acid production in engineered yeast."
    Science.experimentalObservation
    Science.sourceBacked
    "https://doi.org/10.1038/s41467-022-28386-6"
    "Source-bounded article observation. It is not independent repetition or a universal flux mechanism."

analyticIdentityObservation : Science.ScientificMechanismReceipt
analyticIdentityObservation =
  Science.scientific-mechanism-receipt
    "Wong 2022 analytical product evidence"
    "Authors report comparisons supporting D-lysergic-acid identity."
    Science.experimentalObservation
    Science.sourceBacked
    "https://doi.org/10.1038/s41467-022-28386-6"
    "Article Fig. 5 and cited Supplementary Tables/Figures; raw source-data reanalysis has not been completed here."

engineeringScaleProjection : Science.ScientificMechanismReceipt
engineeringScaleProjection =
  Science.scientific-mechanism-receipt
    "Wong 2022 authors' industrial scaling discussion"
    "Authors discuss a hypothetical larger-scale production scenario."
    Science.sourceInterpretation
    Science.preliminary
    "https://doi.org/10.1038/s41467-022-28386-6"
    "Not an observed industrial endpoint and not an independently calibrated scale law."

canonicalScientificReadings : List Science.ScientificMechanismReceipt
canonicalScientificReadings =
  productionObservation
  ∷ analyticIdentityObservation
  ∷ engineeringScaleProjection
  ∷ []

------------------------------------------------------------------------
-- Existing reverse-obligation vocabulary, no second review ontology.
------------------------------------------------------------------------

sourceDataObligation : Science.ScientificReverseObligation
sourceDataObligation =
  Science.scientific-reverse-obligation
    "Wong 2022 source-data tables"
    Science.uncertaintyReceipt
    "Revision-bound source data and replicate-specific numeric uncertainty receipt"
    "Support a reviewer-indexed uncertainty observation of the cited experimental results"
    "Cannot create a laboratory replication or a transferable growth/flux law"

sampleIdentityObligation : Science.ScientificReverseObligation
sampleIdentityObligation =
  Science.scientific-reverse-obligation
    "Wong 2022 product-to-database identity"
    Science.mechanismToObservationWeld
    "Exact compound/charge/stereochemistry plus assay specimen identity evidence"
    "Admit a bounded experiment-to-registry cross-reference"
    "Cannot identify D-lysergic acid with LSD or import receptor activity"

physicalNetworkObligation : Science.ScientificReverseObligation
physicalNetworkObligation =
  Science.scientific-reverse-obligation
    "Wong 2022 yeast metabolic network"
    Science.constitutiveParameterReceipt
    "Source-matched organism, compartments, reaction states, units and independent kinetic/transport evidence"
    "Admit physically justified parameters to the existing metabolic model"
    "Cannot infer internal or exchange fluxes from a titre or CID alone"

independentReplicationObligation : Science.ScientificReverseObligation
independentReplicationObligation =
  Science.scientific-reverse-obligation
    "Wong 2022 reported product evidence"
    Science.independentReplicationReceipt
    "Independent source/assay analysis or externally reported replication with matching scope"
    "Provide separately attributed validation status if authenticated"
    "Cannot be paid by the original article's authorship or DOI"

canonicalWongEvidenceObligations :
  List Science.ScientificReverseObligation
canonicalWongEvidenceObligations =
  sourceDataObligation
  ∷ sampleIdentityObligation
  ∷ physicalNetworkObligation
  ∷ independentReplicationObligation
  ∷ []

------------------------------------------------------------------------
-- Real existing stoichiometric theorem, conditional on actual bridge data.
--
-- No source-paid network instance is claimed. Given a legitimate original
-- `MetabolicStoichiometricBridge`, inherit the pre-existing conservation
-- certificate without reproving, strengthening, or misattributing it.
------------------------------------------------------------------------

existingInternalConservation :
  (network : Metabolic.OpenMetabolicNetwork) →
  (bridge : Stoich.MetabolicStoichiometricBridge network) →
  Stoich.MetabolicStoichiometricCertificate bridge
existingInternalConservation network bridge =
  Stoich.certifyMetabolicStoichiometry bridge

record UnpaidEmpiricalTransport
    (network : Metabolic.OpenMetabolicNetwork) : Set₁ where
  field
    sourceExperiment : Wong.BoundedCrossDomainContext
    reportedOneLitre : Ledger.IndexedEndpoint Core.oneLitreBioreactor
    reportedFourLitre : Ledger.IndexedEndpoint Core.fourLitreBioreactor

    sameOrganismAndStatePaid : Bool
    sameOrganismAndStatePaidIsFalse :
      sameOrganismAndStatePaid ≡ false

    sameCompartmentAndTimePaid : Bool
    sameCompartmentAndTimePaidIsFalse :
      sameCompartmentAndTimePaid ≡ false

    physicalFluxUnitsPaid : Bool
    physicalFluxUnitsPaidIsFalse :
      physicalFluxUnitsPaid ≡ false

    independentKineticsPaid : Bool
    independentKineticsPaidIsFalse :
      independentKineticsPaid ≡ false

-- This receipt is explicitly parametric in a *pre-existing* network object;
-- supplying the object does not mean the paper's network has been realised.
currentUnpaidEmpiricalTransport :
  (network : Metabolic.OpenMetabolicNetwork) →
  UnpaidEmpiricalTransport network
currentUnpaidEmpiricalTransport network = record
  { sourceExperiment = Wong.boundedCrossDomainContextReceipt
  ; reportedOneLitre = Ledger.oneLitreIndexed
  ; reportedFourLitre = Ledger.fourLitreIndexed
  ; sameOrganismAndStatePaid = false
  ; sameOrganismAndStatePaidIsFalse = refl
  ; sameCompartmentAndTimePaid = false
  ; sameCompartmentAndTimePaidIsFalse = refl
  ; physicalFluxUnitsPaid = false
  ; physicalFluxUnitsPaidIsFalse = refl
  ; independentKineticsPaid = false
  ; independentKineticsPaidIsFalse = refl
  }
