module DASHI.Culture.MissingDeceasedTwentyScientistRound14OperatorFactorisationProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
import DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorFactorisationExact as F
import DASHI.Culture.MissingDeceasedTwentyScientistScientificOperatorBidiExact as B

record Round14ScienceProgress : Set where
  constructor round14-science-progress
  field
    person : String
    operatorFamilies : String
    factorisationPaid : Bool
    round14Delta : String
    nextScienceLeaf : String

open Round14ScienceProgress public

nuno = round14-science-progress "Nuno F. G. Loureiro" "field/plasma/precision-force comparator" true "factor reduced-plasma evolution through model/apparatus-to-observable comparator" "source-exact Viriato benchmark replay"
leblanc = round14-science-progress "Joshua Kyle LeBlanc" "resilient sensing/control/verification" true "factor FSP environment-sensor-diagnostic-response chain through resilient-control operator" "named sensor qualification/failure/autonomous-response matrix"
maiwald = round14-science-progress "Frank W. Maiwald" "weak-signal inverse inference + molecular measurement" true "dual factorisation exposes both spectral inverse problem and excitation-to-readout measurement" "raw action-spectrum intensities/calibration"
reza = round14-science-progress "Monica Jacinto / Monica Reza" "materials/process/structure-property" true "factor composition/process-to-strength/burn vector through materials operator" "MONDALOY/enamel process and qualification window"
grillmair = round14-science-progress "Carl J. Grillmair" "weak-signal inverse inference" true "canonical weak-signal fibre: catalogue/filter/distance scan -> stream candidate -> orbit-family residual" "catalogue/filter/orbit-uncertainty replay"
hicks = round14-science-progress "Michael David Hicks" "weak-signal inverse inference" true "factor photometric time series -> phase structure -> physical-model fibre" "calibrated lightcurve/viewing-geometry replay"
mccasland = round14-science-progress "William Neil McCasland" "resilient sensing/control/verification" true "factor failure-family Gramian placement through robustness operator" "historical plant/candidate/failure-family source replay"
chavez = round14-science-progress "Anthony Chavez" "gated" false "no operator family assigned across unpaid missing-person/LANL identity seam" "pay identity weld, then recover exact Scorpius subsystem science"
thomas = round14-science-progress "Jason R. Thomas" "weak-signal inverse inference + molecular measurement" true "factor screen/readout -> target candidate and perturbation-to-readout assay through two reusable families" "Thomas-authored assay plus direct-target validation"
amy = round14-science-progress "Amy Eskridge" "field/plasma/precision-force comparator (gated)" false "retain programme-level comparator family without manufacturing executable Amy science" "Amy-authored/recorded equations or apparatus object"
ning = round14-science-progress "Ning Li" "field/plasma/precision-force comparator" true "factor static/rotating YBCO regimes through controlled comparator/null-result operator" "later apparatus/control/calibration comparator replay"
chen = round14-science-progress "Chen Shuming" "resilient verification + classification/evidence" true "dual factorisation captures graph conformance as assurance and evidence-to-decision" "source graph/stimulus/coverage/mismatch replay"
feng = round14-science-progress "Feng Yanghe" "classification/evidence/governance" true "factor noisy-label Bayesian methods through evidence-to-classification operator" "source equations/data/noise-model replay"
zhou = round14-science-progress "Zhou Guangyuan" "materials/process/structure-property" true "factor aerogel synthesis/network state to thermal-property vector" "multi-sample synthesis/property uncertainty table"
liu = round14-science-progress "Liu Donghao" "classification/evidence/governance" true "factor DSMM lifecycle evidence to maturity assessment without calling it ML" "authored rubric/scoring assessed example"
zhangXiaoxin = round14-science-progress "Zhang Xiaoxin" "weak-signal inverse inference" true "factor whitening/CEEMDAN/CWT precursor extraction through weak-signal operator" "exact decomposition parameters/code/data replay"
zhangDaibing = round14-science-progress "Zhang Daibing" "resilient sensing/control/verification" true "factor sensing/localisation/guidance/control through resilient-control operator" "one DOI dynamics/control/test replay"
liMinyong = round14-science-progress "Li Minyong" "molecular measurement" true "factor wavelength/photoswitch/binding/readout through molecular operator" "exact compound/probe source replay"
fang = round14-science-progress "Fang Daining" "materials/process/structure-property" true "factor unit-cell/design variables through energy/eigenmode to dispersion property vector" "full energy functional/geometry/band arrays"
yan = round14-science-progress "Yan Hong" "resilient sensing/control/verification" true "factor actuator/inlet state to shock-boundary-layer response through resilient-control operator" "source geometry/heat model/mesh/response curves"

round14TwentyScientistProgress : List Round14ScienceProgress
round14TwentyScientistProgress =
  nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷
  thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷
  zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round14ScientificCohortCount : Nat
round14ScientificCohortCount = 20

round14PaidFactorisationCount : Nat
round14PaidFactorisationCount = 18

round14GatedFactorisationCount : Nat
round14GatedFactorisationCount = 2

round14EveryScientistTouched : Bool
round14EveryScientistTouched = true

round14LedgerCountMatches : F.scientificOperatorFactorisationCount ≡ 20
round14LedgerCountMatches = refl

round14OperatorBidiRoutesReuse : Bool
round14OperatorBidiRoutesReuse = B.operatorBidiCanRouteScientificReuse
