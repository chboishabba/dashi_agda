module DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorBidiExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)
import DASHI.Core.ScientificOperatorFamilyExact as O
import DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorFactorisationExact as L

------------------------------------------------------------------------
-- SCIENCE-ONLY OPERATOR BIDI
--
-- Forward: scientist/domain science -> reusable operator role.
-- Reverse: desired operator role -> candidate science fibres + missing science.
-- Historical deployment, possession, custody and events are outside this BIDI.
------------------------------------------------------------------------

data ScientificRoleQuery : Set where
  weakSignalRole resilientControlRole materialsProcessRole : ScientificRoleQuery
  molecularMeasurementRole fieldComparatorRole classificationEvidenceRole : ScientificRoleQuery

familyForRole : ScientificRoleQuery → O.ScientificOperatorFamily
familyForRole weakSignalRole = O.weakSignalInverseInference
familyForRole resilientControlRole = O.resilientSensingControlVerification
familyForRole materialsProcessRole = O.materialsProcessStructureProperty
familyForRole molecularMeasurementRole = O.molecularSpectroscopyChemicalBiology
familyForRole fieldComparatorRole = O.fieldPlasmaPrecisionForceDiscrimination
familyForRole classificationEvidenceRole = O.classificationEvidenceGovernance

reusableRole : O.ScientificOperatorFamily → String
reusableRole O.weakSignalInverseInference = "weak-signal extraction plus uncertainty-aware inverse inference"
reusableRole O.resilientSensingControlVerification = "sensing/verification/estimation plus robust response"
reusableRole O.materialsProcessStructureProperty = "design/process-to-structure/property transformation plus reverse design"
reusableRole O.molecularSpectroscopyChemicalBiology = "molecular perturbation/excitation-to-readout measurement and target/configuration inference"
reusableRole O.fieldPlasmaPrecisionForceDiscrimination = "governing-model/apparatus-to-observable comparator and null/residual discrimination"
reusableRole O.classificationEvidenceGovernance = "uncertain evidence-to-attributable class/verification/assessment state"

forwardRole : L.ScientistOperatorFactorisation → List String
forwardRole row = map reusableRole (L.families row)

record ReverseScientificObligation : Set where
  constructor reverse-scientific-obligation
  field
    query : ScientificRoleQuery
    family : O.ScientificOperatorFamily
    candidateFibres : List String
    missingScientificCoordinate : String
    boundedReading : String

open ReverseScientificObligation public

weakSignalReverse : ReverseScientificObligation
weakSignalReverse = reverse-scientific-obligation weakSignalRole O.weakSignalInverseInference
  ("Grillmair stellar streams" ∷ "Hicks small-body photometry" ∷ "Zhang Xiaoxin space-weather forecast" ∷ "Maiwald action spectroscopy" ∷ "Thomas target deconvolution" ∷ [])
  "domain-specific raw observations, observation/filter model and uncertainty needed to shrink each inverse fibre"
  "Candidate fibres share inverse-inference geometry only; their likelihoods, equations and empirical semantics are not interchangeable."

resilientControlReverse : ReverseScientificObligation
resilientControlReverse = reverse-scientific-obligation resilientControlRole O.resilientSensingControlVerification
  ("LeBlanc FSP I&C" ∷ "McCasland flexible-structure placement" ∷ "Zhang Daibing UAV control" ∷ "Chen hardware verification" ∷ "Yan flow control" ∷ [])
  "source dynamics/environment, sensing/verification semantics, failure family and response/qualification evidence"
  "Verification, placement, autonomy and flow control share robustness structure without sharing plant physics."

materialsProcessReverse : ReverseScientificObligation
materialsProcessReverse = reverse-scientific-obligation materialsProcessRole O.materialsProcessStructureProperty
  ("Reza oxygen-service alloy" ∷ "Zhou polyimide aerogel" ∷ "Fang active metamaterial" ∷ [])
  "process/design state, latent structure, multi-sample property vectors and uncertainty"
  "Shared process-to-property geometry does not create one material law or manufacturing route."

molecularMeasurementReverse : ReverseScientificObligation
molecularMeasurementReverse = reverse-scientific-obligation molecularMeasurementRole O.molecularSpectroscopyChemicalBiology
  ("Maiwald action spectroscopy" ∷ "Thomas chemical-biology assays" ∷ "Li Minyong photopharmacology" ∷ [])
  "source perturbation/excitation, calibration, raw response and direct molecular/target validation"
  "Shared measurement geometry does not make photodissociation, biochemical signalling and photoswitch pharmacology the same mechanism."

fieldComparatorReverse : ReverseScientificObligation
fieldComparatorReverse = reverse-scientific-obligation fieldComparatorRole O.fieldPlasmaPrecisionForceDiscrimination
  ("Loureiro reduced plasma" ∷ "Ning Li YBCO comparator" ∷ "Amy Eskridge programme-level mechanism map" ∷ [])
  "source governing/model coordinates, controlled apparatus regimes and calibrated comparator residuals"
  "Amy remains authorship/programme-gated; inclusion as a candidate family does not create executable Amy science."

classificationEvidenceReverse : ReverseScientificObligation
classificationEvidenceReverse = reverse-scientific-obligation classificationEvidenceRole O.classificationEvidenceGovernance
  ("Feng noisy-label classification" ∷ "Liu DSMM assessment" ∷ "Chen hardware verification" ∷ [])
  "source decision/scoring rule, labelled/evidence examples, coverage/error semantics and attributable outputs"
  "Machine classification, governance maturity and hardware verification remain different sciences despite a shared evidence-to-decision operator."

reverseScientificObligations : List ReverseScientificObligation
reverseScientificObligations =
  weakSignalReverse ∷ resilientControlReverse ∷ materialsProcessReverse ∷
  molecularMeasurementReverse ∷ fieldComparatorReverse ∷ classificationEvidenceReverse ∷ []

operatorBidiDoesNotPayHistoricalDeployment : Bool
operatorBidiDoesNotPayHistoricalDeployment = false

operatorBidiDoesNotPayPersonPossession : Bool
operatorBidiDoesNotPayPersonPossession = false

operatorBidiDoesNotPayCustody : Bool
operatorBidiDoesNotPayCustody = false

operatorBidiDoesNotPayEventCause : Bool
operatorBidiDoesNotPayEventCause = false

operatorBidiCanRouteScientificReuse : Bool
operatorBidiCanRouteScientificReuse = true
