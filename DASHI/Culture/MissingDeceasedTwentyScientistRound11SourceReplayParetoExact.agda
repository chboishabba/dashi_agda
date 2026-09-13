module DASHI.Culture.MissingDeceasedTwentyScientistRound11SourceReplayParetoExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

record Round11ScientistProgress : Set where
  constructor round11-scientist-progress
  field
    person : String
    round11Delta : String
    newReplayPromotion : Bool
    nextScienceLeaf : String
    nextCustodyLeaf : String

open Round11ScientistProgress public

nuno = round11-scientist-progress "Nuno F. G. Loureiro" "retained executable plasma machinery; source benchmark remains next" false "one published Viriato initial condition/closure/discretisation/output replay" "repository maintainer, grant reassignment and simulation-state custodian"
leblanc = round11-scientist-progress "Joshua Kyle LeBlanc" "retained source-exact FSP envelope; device qualification remains next" false "named device qualification/calibration/failure row" "first dated post-loss SNP I&C TechMat roster/handover"
maiwald = round11-scientist-progress "Frank W. Maiwald" "supporting-information inventory now narrows the missing replay to experimental intensities/calibration" true "raw ValH+ action-spectrum intensity array and absolute calibration" "raw/reduced spectra, notebooks and SURP handover"
reza = round11-scientist-progress "Monica Jacinto / Monica Reza" "retained alloy/process finite owners" false "MONDALOY/enamel source-exact composition/process/qualification window" "Boeing/UTC/Rocketdyne/Aerojet assignment and process custodian"
grillmair = round11-scientist-progress "Carl J. Grillmair" "source-exact 2017 four-stream ensemble geometry now bound into replay BIDI" true "exact catalogue slice, matched-filter weights and orbit-fit uncertainty" "stream maps/catalogues/orbit-fit or unfinished-manuscript custodian"
hicks = round11-scientist-progress "Michael David Hicks" "source-exact Florence campaign receipt now binds Hicks to 2017-08-30 Table Mountain lightcurve and 2.4 h campaign period" true "Hicks lightcurve array, viewing geometry and calibration" "2022 JPL separation and unfinished observing/reduction/data handover"
mccasland = round11-scientist-progress "William Neil McCasland" "retained executable Gramian machinery" false "published plant matrices/candidate locations/failure family replay" "dated DBE status and 2025-2026 client/programme carrier"
chavez = round11-scientist-progress "Anthony Chavez" "identity gate retained; no replay crosses missing-person/LANL seam" false "after identity weld, exact Scorpius subsystem geometry/calibration/design responsibility" "primary same-person weld"
thomas = round11-scientist-progress "Jason R. Thomas" "retained finite signalling mechanism" false "source assay counts plus direct-target/ferritinophagy validation" "lab/project/data successor and final ME carrier"
amy = round11-scientist-progress "Amy Eskridge" "technical-authorship gate retained" false "Amy-authored/recorded equations, apparatus, deck or reviewed manuscript" "NF-1676/EDAA/STRIVES plus Institute derivative/handover identity"
ning = round11-scientist-progress "Ning Li" "retained source-exact static/rotating apparatus comparison" false "later AC Gravity/NASA/Army apparatus geometry, controls and calibration" "FY2001 DoD row, Army SOW, closeout/result and apparatus custody"
chen = round11-scientist-progress "Chen Shuming" "retained finite hardware-verification carrier" false "source graph semantics, stimuli, coverage and mismatch example" "processor-specific responsibility and successor"
feng = round11-scientist-progress "Feng Yanghe" "retained finite classifier carrier; War Skull seam still separate" false "source equations/data/noise parameters and one classifier replay" "post-2023 War Skull code/project lead and primary event carrier"
zhou = round11-scientist-progress "Zhou Guangyuan" "source property portfolio now bound as replay: shrinkage/porosity/surface-area/thermal-stability/conductivity coordinates" true "exact multi-sample synthesis/property table with uncertainty" "Hu Yanming/Wang Rui patent/process/enterprise-transfer custody"
liu = round11-scientist-progress "Liu Donghao" "retained finite DSMM lifecycle carrier" false "authored maturity rubric/scoring and one assessed example" "dated Liu-to-Liao governance transition and project custody"
zhangXiaoxin = round11-scientist-progress "Zhang Xiaoxin" "source replay deepened to an explicit 129/166 finite recall witness inside the 229-event carrier" true "exact whitening/CEEMDAN/CWT parameters, code/data and operational threshold" "dated NSMC/Fengyun successor and payload/ground-system custody"
zhangDaibing = round11-scientist-progress "Zhang Daibing" "retained finite autonomy/control carrier" false "one DOI source-exact dynamics/control/test replay" "Yunzhihang/NUDT project and code custodian"
liMinyong = round11-scientist-progress "Li Minyong" "retained finite photopharmacology/probe carrier" false "one exact molecule/probe wavelength/state/affinity/dose/readout replay" "post-loss lab/project/patent/student custodian"
fang = round11-scientist-progress "Fang Daining" "retained source replay of inverse-design objective/negative-group-velocity claim" false "full energy functional, unit-cell geometry/constants and band arrays" "post-loss BIT project/code/IP handover"
yan = round11-scientist-progress "Yan Hong" "retained source replay of Mach-5 actuator cases" false "source geometry, heat model and shock/separation curves" "named NPU project/code/data successor"

round11TwentyScientistProgress : List Round11ScientistProgress
round11TwentyScientistProgress = nuno ∷ leblanc ∷ maiwald ∷ reza ∷ grillmair ∷ hicks ∷ mccasland ∷ chavez ∷ thomas ∷ amy ∷ ning ∷ chen ∷ feng ∷ zhou ∷ liu ∷ zhangXiaoxin ∷ zhangDaibing ∷ liMinyong ∷ fang ∷ yan ∷ []

round11ScientificCohortCount : Nat
round11ScientificCohortCount = 20

round11NewReplayPromotionCount : Nat
round11NewReplayPromotionCount = 5

round11EveryScientistTouched : Bool
round11EveryScientistTouched = true

sourceReplayDoesNotPayCustody : Bool
sourceReplayDoesNotPayCustody = false

sourceReplayDoesNotPayHistoricalUse : Bool
sourceReplayDoesNotPayHistoricalUse = false

sourceReplayDoesNotPayEventCause : Bool
sourceReplayDoesNotPayEventCause = false
