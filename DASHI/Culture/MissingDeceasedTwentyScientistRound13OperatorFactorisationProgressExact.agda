module DASHI.Culture.MissingDeceasedTwentyScientistRound13OperatorFactorisationProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
import DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorFactorisationExact as F
import DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorBidiExact as B

record Round13ScienceProgress : Set where
  constructor round13-science-progress
  field
    person : String
    operatorFamilies : String
    factorisationPaid : Bool
    round13Delta : String
    nextScienceLeaf : String

open Round13ScienceProgress public

nuno = round13-science-progress "Nuno F. G. Loureiro" "field/plasma/precision-force comparator" true "factor reduced-plasma evolution through model/apparatus-to-observable comparator" "source-exact Viriato benchmark replay"
leblanc = round13-science-progress "Joshua Kyle LeBlanc" "resilient sensing/control/verification" true "factor FSP environment-sensor-diagnostic-response chain through resilient-control operator" "named sensor qualification/failure/autonomous-response matrix"
maiwald = round13-science-progress "Frank W. Maiwald" "weak-signal inverse inference + molecular measurement" true "dual factorisation exposes both spectral inverse problem and excitation-to-readout measurement" "raw action-spectrum intensities/calibration"
reza = round13-science-progress "Monica Jacinto / Monica Reza" "materials/process/structure-property" true "factor composition/process-to-strength/burn vector through materials operator" "MONDALOY/enamel process and qualification window"
grillmair = round13-science-progress "Carl J. Grillmair" "weak-signal inverse inference" true "canonical weak-signal fibre: catalogue/filter/distance scan -> stream candidate -> orbit-family residual" "catalogue/filter/orbit-uncertainty replay"
hicks = round13-science-progress "Michael David Hicks" "weak-signal inverse inference" true "factor photometric time series -> phase structure -> physical-model fibre" "calibrated lightcurve/viewing-geometry replay"
mccasland = round13-science-progress "William Neil McCasland" "resilient sensing/control/verification" true "factor failure-family Gramian placement through robustness operator" "historical plant/candidate/failure-family source replay"
chavez = round13-science-progress "Anthony Chavez" "gated" false "no operator family assigned across unpaid missing-person/LANL identity seam" "pay identity weld, then recover exact Scorpius subsystem science"
thomas = round13-science-progress "Jason R. Thomas" "weak-signal inverse inference + molecular measurement" true "factor screen/readout -> target candidate and perturbation-to-readout assay through two reusable families" "Thomas-authored assay plus direct-target validation"
amy = round13-science-progress "Amy Eskridge" "field/plasma/precision-force comparator (gated)" false "retain programme-level comparator family without manufacturing executable Amy science" "Amy-authored/recorded equations or apparatus object"
ning = round13-science-progress "Ning Li" "field/plasma/precision-force comparator" true "factor static/rotating YBCO regimes through controlled comparator/null-result operator" "later apparatus/control/calibration comparator replay"
chen = round13-science-progress "Chen Shuming" "resilient verification + classification/evidence" true "dual factorisation captures graph conformance as assurance and evidence-to-decision" "source graph/stimulus/coverage/mismatch replay"
feng = round13-science-progress "Feng Yanghe" "classification/evidence/governance" true "factor noisy-label Bayesian methods through evidence-to-classification operator" "source equations/data/noise-model replay"
zhou = round13-science-progress "Zhou Guangyuan" "materials/process/structure-property" true "factor aerogel synthesis/network state to thermal-property vector" "multi-sample synthesis/property uncertainty table"
liu = round13-science-progress "Liu Donghao" "classification/evidence/governance" true "factor DSMM lifecycle evidence to maturity assessment without calling it ML" "authored rubric/scoring assessed example"
zhangXiaoxin = round13-science-progress "Zhang Xiaoxin" "weak-signal inverse inference" true "factor whitening/CEEMDAN/CWT precursor extraction through weak-signal operator" "exact decomposition parameters/code/data replay"
zhangDaibing = round13-science-progress "Zhang Daibing" "resilient sensing/control/verification" true "factor sensing/localisation/guidance/control through resilient-control operator" "one DOI dynamics/control/test replay"
liMinyong = round13-science-progress "Li Minyong" "molecular measurement" true "factor wavelength/photoswitch/binding/readout through molecular operator" "exact compound/probe source replay"
fang = round13-science-progress "Fang Daining" "materials/process/structure-property" true "factor unit-cell/design variables through energy/eigenmode to dispersion property vector" "full energy functional/geometry/band arrays"
yan = round13-science-progress "Yan Hong" "resilient sensing/control/verification" true "factor actuator/inlet state to shock-boundary-layer response through resilient-control operator" "source geometry/heat model/mesh/response curves"

round13TwentyScientistProgress : List Round13ScienceProgress
round13TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round13ScientificCohortCount : Nat
round13ScientificCohortCount = 20

round13PaidFactorisationCount : Nat
round13PaidFactorisationCount = 18

round13GatedFactorisationCount : Nat
round13GatedFactorisationCount = 2

round13EveryScientistTouched : Bool
round13EveryScientistTouched = true

round13LedgerCountMatches : F.scientificOperatorFactorisationCount ≡ 20
round13LedgerCountMatches = refl

round13OperatorBidiRoutesReuse : Bool
round13OperatorBidiRoutesReuse = B.operatorBidiCanRouteScientificReuse
