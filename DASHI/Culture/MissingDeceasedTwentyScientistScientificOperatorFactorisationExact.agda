module DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorFactorisationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import DASHI.Core.ScientificOperatorFamilyExact as O

------------------------------------------------------------------------
-- ALL-TWENTY SCIENTIFIC OPERATOR FACTORISATION LEDGER
------------------------------------------------------------------------

data FactorisationStatus : Set where paid gated : FactorisationStatus

record ScientistOperatorFactorisation : Set where
  constructor scientist-operator-factorisation
  field
    person : String
    families : List O.ScientificOperatorFamily
    domainOwner : String
    status : FactorisationStatus
    nextScienceLeaf : String

open ScientistOperatorFactorisation public

nuno = scientist-operator-factorisation "Nuno F. G. Loureiro"
  (O.fieldPlasmaPrecisionForceDiscrimination ∷ [])
  "LoureiroViriatoPlasmoidBidiExact / KREHM-Hermite owners" paid
  "source-exact Viriato benchmark replay"

leblanc = scientist-operator-factorisation "Joshua Kyle LeBlanc"
  (O.resilientSensingControlVerification ∷ [])
  "LeBlancFissionSurfacePowerICBidiExact / NumericEnvelopeExact" paid
  "named sensor/device qualification and autonomous-response matrix"

maiwald = scientist-operator-factorisation "Frank W. Maiwald"
  (O.weakSignalInverseInference ∷ O.molecularSpectroscopyChemicalBiology ∷ [])
  "MaiwaldActionSpectroscopyBidiExact / SourceReplayDepthExact" paid
  "raw experimental action-spectrum intensity/calibration replay"

reza = scientist-operator-factorisation "Monica Jacinto / Monica Reza"
  (O.materialsProcessStructureProperty ∷ [])
  "RezaBurnResistantAlloyBidiExact / CompositionTradeoffExact" paid
  "source-exact descendant process/qualification window"

grillmair = scientist-operator-factorisation "Carl J. Grillmair"
  (O.weakSignalInverseInference ∷ [])
  "GrillmairStellarStreamBidiExact / SourceReplayExact" paid
  "catalogue/filter/distance-scan/orbit uncertainty replay"

hicks = scientist-operator-factorisation "Michael David Hicks"
  (O.weakSignalInverseInference ∷ [])
  "HicksSmallBodyPhotometryBidiExact / SourceReplayExact" paid
  "calibrated Table Mountain lightcurve and viewing-geometry replay"

mccasland = scientist-operator-factorisation "William Neil McCasland"
  (O.resilientSensingControlVerification ∷ [])
  "McCaslandFaultTolerantFlexibleStructureControlBidiExact / finite Gramian engine" paid
  "historical source plant matrices/candidate/failure-family replay"

chavez = scientist-operator-factorisation "Anthony Chavez"
  []
  "AnthonyChavezScorpiusBidiExact" gated
  "pay same-person identity before assigning a reusable operator family to the missing-person fibre"

thomas = scientist-operator-factorisation "Jason R. Thomas"
  (O.weakSignalInverseInference ∷ O.molecularSpectroscopyChemicalBiology ∷ [])
  "JasonThomasSignallingBidiExact / finite target-deconvolution owners" paid
  "one Thomas-authored assay dataset and direct-target validation replay"

amy = scientist-operator-factorisation "Amy Eskridge"
  (O.fieldPlasmaPrecisionForceDiscrimination ∷ [])
  "AmyEskridgeGravityMechanismCrossPollinationExact" gated
  "recover Amy-authored/recorded equations or apparatus before executable factorisation"

ning = scientist-operator-factorisation "Ning Li"
  (O.fieldPlasmaPrecisionForceDiscrimination ∷ [])
  "LiTorr theory + NingLi YBCO apparatus comparison" paid
  "later source-exact apparatus/control/calibration comparator replay"

chen = scientist-operator-factorisation "Chen Shuming"
  (O.resilientSensingControlVerification ∷ O.classificationEvidenceGovernance ∷ [])
  "ChenShumingGraphHardwareVerificationBidiExact / FiniteWitnessExact" paid
  "source graph/stimulus/coverage/mismatch replay"

feng = scientist-operator-factorisation "Feng Yanghe"
  (O.classificationEvidenceGovernance ∷ [])
  "FengYangheMilitaryAIGameStatisticsBidiExact / ClassificationFiniteWitnessExact" paid
  "source equations/data/noise-parameter classifier replay"

zhou = scientist-operator-factorisation "Zhou Guangyuan"
  (O.materialsProcessStructureProperty ∷ [])
  "ZhouGuangyuanPolyimideAerogelBidiExact / ProcessPropertySourceReplayExact" paid
  "multi-sample process/property/uncertainty replay"

liu = scientist-operator-factorisation "Liu Donghao"
  (O.classificationEvidenceGovernance ∷ [])
  "LiuDonghaoDSMMBidiExact / DSMMFiniteWitnessExact" paid
  "authored rubric/scoring and assessed source example"

zhangXiaoxin = scientist-operator-factorisation "Zhang Xiaoxin"
  (O.weakSignalInverseInference ∷ [])
  "ZhangXiaoxinGeomagneticForecastBidiExact / ForecastRecallArithmeticExact" paid
  "exact CEEMDAN/CWT parameters, precursor rule and runnable source data"

zhangDaibing = scientist-operator-factorisation "Zhang Daibing"
  (O.resilientSensingControlVerification ∷ [])
  "ZhangDaibingUAVControlBidiExact / UAVControlFiniteWitnessExact" paid
  "one DOI source dynamics/control/test replay"

liMinyong = scientist-operator-factorisation "Li Minyong"
  (O.molecularSpectroscopyChemicalBiology ∷ [])
  "LiMinyongPhotopharmacologyBidiExact / PhotopharmacologyFiniteWitnessExact" paid
  "one exact compound/probe wavelength-state-binding-readout replay"

fang = scientist-operator-factorisation "Fang Daining"
  (O.materialsProcessStructureProperty ∷ [])
  "FangDainingActiveMechanicalMetamaterialBidiExact / InverseDesignSourceReplayExact" paid
  "full energy functional, unit-cell geometry/constants and band arrays"

yan = scientist-operator-factorisation "Yan Hong"
  (O.resilientSensingControlVerification ∷ [])
  "YanHongHypersonicFlowControlBidiExact / ThermalExcitationSourceReplayExact" paid
  "source geometry/heat-model/mesh/shock-response replay"

scientificOperatorFactorisations : List ScientistOperatorFactorisation
scientificOperatorFactorisations =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

scientificOperatorFactorisationCount : Nat
scientificOperatorFactorisationCount = 20

paidScienceFactorisationCount : Nat
paidScienceFactorisationCount = 18

gatedScienceFactorisationCount : Nat
gatedScienceFactorisationCount = 2

everyScientistRepresented : Bool
everyScientistRepresented = true

overlappingOperatorFamiliesAllowed : Bool
overlappingOperatorFamiliesAllowed = true

sharedOperatorFamilyImpliesSameMechanism : Bool
sharedOperatorFamilyImpliesSameMechanism = false

sharedOperatorFamilyImpliesCollaboration : Bool
sharedOperatorFamilyImpliesCollaboration = false
