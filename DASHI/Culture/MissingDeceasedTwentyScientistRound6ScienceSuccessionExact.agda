module DASHI.Culture.MissingDeceasedTwentyScientistRound6ScienceSuccessionExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- ROUND 6: SCIENCE PROOF DEBT + CAPABILITY SUCCESSION DEBT
--
-- Every retained scientist carries both a concrete science/engineering kernel
-- and a distinct succession/custody leaf.  Science adjacency cannot create a
-- common cause; institutional survival cannot create exact capability transfer.
------------------------------------------------------------------------

data Round6Side : Set where us china : Round6Side

data ScienceDebtKind : Set where
  equationDepth apparatusDepth dataDepth processDepth algorithmDepth identityWeldDepth : ScienceDebtKind

data SuccessionDebtKind : Set where
  repositoryCustody dataCustody calibrationCustody processCustody projectLeadership ipCustody identityWeld : SuccessionDebtKind

record Round6Progress : Set where
  constructor round6-progress
  field
    person : String
    side : Round6Side
    scienceKernel : String
    scienceObject : String
    stableIdentifier : String
    scienceDebtKind : ScienceDebtKind
    scienceProofLeaf : String
    freshScienceDelta : String
    successionDebtKind : SuccessionDebtKind
    successionLeaf : String
    scienceLeafPaid : Bool
    successionLeafPaid : Bool

open Round6Progress public

------------------------------------------------------------------------
-- United States (11)
------------------------------------------------------------------------

nunoLoureiroRound6 = round6-progress
  "Nuno F. G. Loureiro" us
  "Viriato KREHM/KRMHD Fourier-Hermite plasma dynamics, reconnection, plasmoid instability and kinetic-Alfven turbulence"
  "Viriato/KREHM implementation and Hermite-moment plasma equations"
  "arXiv:1505.02649"
  equationDepth
  "weld the exact KREHM/KRMHD equations, Hermite closures, numerical discretisation and finite benchmarks to the repo Viriato/Hermite owners"
  "fresh audit keeps Viriato as a specific Fourier-Hermite plasma code rather than generic fusion software"
  repositoryCustody
  "named post-loss Viriato/KREHM repository maintainer, grant reassignment and simulation-state custodian"
  false false

joshuaLeBlancRound6 = round6-progress
  "Joshua Kyle LeBlanc" us
  "space-fission instrumentation and controls technology maturation, sensing, qualification and integration"
  "NASA 40 kW FSP I&C technology path / NPIC&HMIT technology gaps"
  "NTRS 20250008475; DOI 10.13182/NPICHMIT25-46370"
  dataDepth
  "recover the exact FICS gap matrix, sensor requirements, qualification envelopes, calibration state and failure-model evidence"
  "fresh NTRS surface preserves the actual I&C executive-committee roles and WBS while remaining a stale post-loss role snapshot"
  calibrationCustody
  "first dated SNP I&C TechMat roster revision plus named successor and calibration/failure/qualification-data handover"
  false false

frankMaiwaldRound6 = round6-progress
  "Frank W. Maiwald" us
  "cryogenic messenger-tag action spectroscopy and quadrupole-ion-trap mass spectrometry for molecular/isomer discrimination"
  "Cryogenic Ion Vibrational Spectroscopy of Protonated Valine: Messenger Tag Effects"
  "DOI 10.1021/acs.jpca.4c03552; PMID 39150465"
  apparatusDepth
  "formalise tagged ion species, trap temperature/state, messenger-tag perturbation, IR scan and fragmentation/action-spectrum mapping"
  "fresh DOI/PMID-level object gives a clean publication manifestation linking Maiwald to the 2024 protonated-valine spectroscopy result"
  dataCustody
  "raw/reduced spectra, calibration files, notebooks and exact 2023 SURP to 2024 publication handover"
  false false

monicaRezaRound6 = round6-progress
  "Monica Jacinto / Monica Reza" us
  "burn-resistant high-strength Ni-Co-Cr-Al-Ti oxygen-service alloy, gamma/gamma-prime microstructure and VIM/VAR process control"
  "Jacinto/Hardwick alloy family plus later oxygen-turbopump MONDALOY application patents"
  "US20030053926A1; US20100266442A1; US20190032604A1"
  processDepth
  "formalise composition and heat/process windows against burn-pressure/tensile tradeoffs, then separate bulk alloy, coating and enamel-overlayer descendants"
  "fresh patent snowball preserves the later turbopump application as an application descendant rather than evidence for exotic provenance"
  processCustody
  "literal assignment/programme chain from Boeing/UTC into Rocketdyne/Aerojet plus 2025 JPL role and process-window custodian"
  false false

carlGrillmairRound6 = round6-progress
  "Carl J. Grillmair" us
  "matched-filter stellar-stream detection, orbit inference and Galactic-potential constraints; separate exoplanet spectroscopy work"
  "Caltech/IPAC stellar-stream publication corpus"
  "DOI 10.3847/1538-4357/aa8872"
  algorithmDepth
  "close the colour-magnitude matched-filter weights, finite stream detection statistic and orbit-fit inference on one source-exact stream"
  "fresh IPAC personnel update shows broad institution-level leadership continuity but no named stellar-stream successor"
  dataCustody
  "named custodian for Grillmair stream maps/catalogues, matched-filter products, orbit fits or unfinished manuscripts"
  false false

michaelHicksRound6 = round6-progress
  "Michael David Hicks" us
  "asteroid/comet photometry and spectrophotometry, rotational/phase inference and archived small-body observing"
  "JPL/TMO and small-body publication corpus"
  "exact DOI set retained in Hicks specific-work owner"
  dataDepth
  "select source-exact lightcurve/spectrophotometry objects and formalise measurement plus uncertainty to rotation/shape/composition inference"
  "science remains observational planetary astronomy; no new source supports propulsion or sensitive-programme promotion"
  dataCustody
  "primary 2022 JPL separation plus unfinished observing, reduction pipeline and dataset handover"
  false false

neilMcCaslandRound6 = round6-progress
  "William Neil McCasland" us
  "fault-tolerant sensor/actuator placement for flexible structures using controllability/observability Gramians and failure-family optimisation"
  "Sensor and Actuator Selection for Fault-Tolerant Control of Flexible Structures"
  "MIT thesis / ACC 1989 / NASA A89-54007"
  algorithmDepth
  "reconstruct the Gramian performance indices, continuous placement relaxation, discrete selection and fault-family objective on a finite beam model"
  "fresh source audit keeps the original control-theory object distinct from later AFRL command and speculative UAP narratives"
  projectLeadership
  "dated DBE Consulting role and exact 2025-2026 client/programme/tasking carrier"
  false false

anthonyChavezRound6 = round6-progress
  "Anthony Chavez" us
  "LANL engineering carrier: DARHT engineering and Scorpius accelerator design; separate permanent-magnet spectrometer publication identity"
  "LANL Summer 2025 Anthony Chavez engineering profile"
  "LANL Summer 2025 profile"
  identityWeldDepth
  "deepen exact Scorpius subsystem/design responsibility only after the missing-person identity is welded to the LANL profile"
  "fresh LANL object remains strong on engineering content but still cannot bridge the identity gap by name alone"
  identityWeld
  "primary same-person receipt joining NM missing-person Anthony Chavez to the LANL engineering-profile carrier"
  false false

jasonThomasRound6 = round6-progress
  "Jason R. Thomas" us
  "STING signalling and VPS34/NCOA4 ferritin degradation/ferritinophagy chemical biology"
  "Thomas signalling corpus and VPS34/NCOA4 mechanism lineage"
  "DOI 10.1038/ncb3053 science-lineage coordinate"
  apparatusDepth
  "recover exact Thomas-authored assay objects and formalise perturbation, target/substrate identification, ferritin turnover and readout chain"
  "fresh search did not produce a stronger exact Thomas-specific mechanism object than the existing repo corpus"
  dataCustody
  "final ME cause/manner plus lab/project/data succession for exact STING/ferritinophagy work"
  false false

amyEskridgeRound6 = round6-progress
  "Amy Eskridge" us
  "engineered-gravity mechanism programme: electrogravitics and field-propulsion mechanism discrimination; conventional scientific authorship remains partly unresolved"
  "HAL5 historical-survey material and claimed 2020 NASA-review object; NTRS 20205010911 only as a comparator"
  "Amy same-object STI identifier unresolved"
  identityWeldDepth
  "recover an Amy-authored or Amy-recorded technical object with equations/apparatus coordinates before welding her programme to POAMS, Li-Torr, Woodward or other mechanism families"
  "fresh public-record review reinforces that NTRS 20205010911 is not Amy authorship and that community retellings cannot fill the missing science object"
  identityWeld
  "Amy-linked NF-1676/EDAA/STRIVES record plus Institute derivative/handover identity"
  false false

ningLiRound6 = round6-progress
  "Ning Li" us
  "superconducting gravitoelectric/gravitomagnetic theory plus static and rotating/AC-field YBCO gravity tests"
  "Li/Torr theory and 1997/1998 YBCO experimental lineage"
  "10.1103/PhysRevD.43.457; 10.1103/PhysRevB.46.5489; 10.1016/S0921-4534(97)01462-7; NTRS 19990019627"
  apparatusDepth
  "reconstruct static versus rotating/AC apparatus, magnetic/thermal/buoyancy controls and observation precision before comparing any later AC Gravity apparatus"
  "fresh source audit again confirms the <2e-8 g static bound and keeps multiple NASA manifestations as one lineage rather than independent replication"
  projectLeadership
  "recover original FY2001 DoD row, Army SOW, closeout/result and exact apparatus continuity from NCC8-124 to DAAH01-01-9-R001"
  false false

------------------------------------------------------------------------
-- China (9)
------------------------------------------------------------------------

chenShumingRound6 = round6-progress
  "Chen Shuming" china
  "hardware/processor verification and indigenous military DSP/flight-control chip development"
  "Simulation-Based Hardware Verification with a Graph-Based Specification plus NUDT Galaxy/Feiteng history"
  "DOI 10.1155/2018/6398616"
  algorithmDepth
  "formalise the graph-based hardware specification, simulation coverage/verification relation and connect it only where source-exact to Chen's processor-development role"
  "fresh DOI-level paper gives a specific hardware-verification science object beyond the generic military-chip label"
  projectLeadership
  "primary event identity and post-loss redistribution of Chen-specific processor/verification responsibility"
  false false

fengYangheRound6 = round6-progress
  "Feng Yanghe" china
  "military wargame decision agents plus multi-group-graph Bayesian classification and noisy-label classification"
  "War Skull II institutional surface and NUDT Press Bayesian/noisy-label monographs"
  "ISBN 978-7-5673-0533-5; ISBN 978-7-5673-0611-0"
  algorithmDepth
  "formalise Bayesian graph classification and noisy-label robustness separately, then require a same-object software/document receipt before mapping either algorithm into War Skull"
  "science remains two partly separate objects: statistical learning methods and wargame-agent engineering"
  repositoryCustody
  "post-2023 War Skull technical lead/code custodian plus primary event carrier"
  false false

zhouGuangyuanRound6 = round6-progress
  "Zhou Guangyuan" china
  "low-shrinkage high-temperature polyimide aerogels using paddle-shaped benzhydrylidenefluorene diamines"
  "Chemical Engineering Journal article 147642"
  "DOI 10.1016/j.cej.2023.147642"
  processDepth
  "formalise monomer/synthesis to shrinkage/porosity to thermal conductivity and thermal-stability response with SI units and measured bounds"
  "fresh publisher surface reconfirms 54.3 mW m^-1 K^-1 at 200 C and the extreme-environment thermal-insulation objective"
  ipCustody
  "map Hu Yanming/Wang Rui successor groups to exact aerogel patents, process windows and enterprise-transfer objects"
  false false

liuDonghaoRound6 = round6-progress
  "Liu Donghao" china
  "DSMM/data-security maturity governance over collection, transmission, storage, processing, exchange and destruction"
  "GB/T 37988-2019 context plus institutional lecture surface"
  "GB/T 37988-2019"
  algorithmDepth
  "recover exact Liu-authored standards contributions, maturity-level assessment rules, papers and patents; do not substitute generic cybersecurity primitives"
  "fresh search did not improve the exact authored-method surface beyond the existing bounded institutional material"
  projectLeadership
  "date Liu-to-Liao governance transition and first post-loss DSMM/project custody"
  false false

zhangXiaoxinRound6 = round6-progress
  "Zhang Xiaoxin" china
  "space-weather prediction and Fengyun monitoring: CME-driven geomagnetic-storm modelling plus payload/ground-system programme leadership"
  "A New Method for Predicting Non-Recurrent Geomagnetic Storms"
  "DOI 10.1029/2023SW003522; ORCID 0000-0002-7759-7402"
  algorithmDepth
  "formalise spectral whitening plus CEEMDAN-CWT prediction pipeline, data split/validation and prediction metrics; keep this separate from payload calibration"
  "fresh publisher metadata explicitly pays Zhang's conceptualisation, supervision, project administration and funding-acquisition roles"
  projectLeadership
  "dated NSMC/Fengyun successor and committee reconstitution plus manuscript chronology for the 2025 FY-4B paper"
  false false

zhangDaibingRound6 = round6-progress
  "Zhang Daibing" china
  "UAV autonomous landing, path following, localisation, formation and unmanned-system control"
  "three DOI-level NUDT/BUAA/Robot publication objects retained in roster owner"
  "10.11887/j.cn.201801023; 10.13700/j.bh.1001-5965.2016.0679; 10.13973/j.cnki.robot.2017.0160"
  algorithmDepth
  "formalise one source-exact guidance/localisation/control law and field-test error/robustness envelope before synthesising the broader UAV capability"
  "fresh search did not surface a stronger primary successor or new DOI beyond the already retained technical corpus"
  projectLeadership
  "primary Yunzhihang governance record and named NUDT/company project custodian"
  false false

liMinyongRound6 = round6-progress
  "Li Minyong" china
  "photopharmacology and fluorescent molecular probes for target visualisation"
  "2025 azobenzene in-vivo photopharmacology review plus alpha1-adrenergic receptor fluorescent-probe patents"
  "DOI 10.1002/med.22120; CN201110101082.5; CN201110100874.0"
  processDepth
  "select an exact photoswitch/probe object and formalise wavelength/state switching, target binding, fluorescence or physiological readout and reversibility"
  "fresh science snowball adds a 2025 DOI-level photopharmacology object and source-exact older fluorescent-probe patent identifiers"
  ipCustody
  "named post-loss lab/project/patent/student custodian and dated Hainan organisational transition"
  false false

fangDainingRound6 = round6-progress
  "Fang Daining" china
  "multifield mechanics and elastic metamaterial inverse design for prescribed eigenmodes/dispersion"
  "Force-field-induced energy-based design method for arbitrary prescribed modes in elastic metamaterials"
  "DOI 10.1016/j.jmps.2025.106144"
  equationDepth
  "formalise force-field-induced energy map to eigenmode/dispersion constraints and the experimentally verified negative-group-velocity case"
  "fresh publisher and institutional metadata confirm the exact 2025 inverse-design object and its experimental band-structure validation"
  projectLeadership
  "post-loss BIT project-level handover for Fang-led advanced-structure/metamaterial/extreme-environment work"
  false false

yanHongRound6 = round6-progress
  "Yan Hong" china
  "supersonic/hypersonic inlet shock-boundary-layer control using thermal excitation, plus plasma-flow-control programme"
  "Control of shock/boundary layer interaction in supersonic inlet using thermal excitation"
  "DOI 10.7638/kqdlxxb-2013.0102"
  apparatusDepth
  "formalise thermal-excitation location/power to shock and separation response using the source-exact inlet configuration; keep later plasma methods as a separate fibre until welded"
  "fresh journal surface gives exact authorship, NPU affiliation, volume/pages and DOI for the thermal-excitation experiment/model"
  projectLeadership
  "dated post-loss NPU committee/project roster naming successor for inlet, plasma-flow-control or numerical-wind-tunnel work"
  false false

------------------------------------------------------------------------
-- Round-6 invariants.
------------------------------------------------------------------------

twentyScientistRound6Progress : List Round6Progress
twentyScientistRound6Progress =
  nunoLoureiroRound6 ∷ joshuaLeBlancRound6 ∷ frankMaiwaldRound6 ∷ monicaRezaRound6 ∷
  carlGrillmairRound6 ∷ michaelHicksRound6 ∷ neilMcCaslandRound6 ∷ anthonyChavezRound6 ∷
  jasonThomasRound6 ∷ amyEskridgeRound6 ∷ ningLiRound6 ∷
  chenShumingRound6 ∷ fengYangheRound6 ∷ zhouGuangyuanRound6 ∷ liuDonghaoRound6 ∷
  zhangXiaoxinRound6 ∷ zhangDaibingRound6 ∷ liMinyongRound6 ∷ fangDainingRound6 ∷
  yanHongRound6 ∷ []

round6ScientificCohortCount : Nat
round6ScientificCohortCount = 20

round6EveryScientistHasScienceKernel : Bool
round6EveryScientistHasScienceKernel = true

round6EveryScientistHasScienceProofLeaf : Bool
round6EveryScientistHasScienceProofLeaf = true

round6EveryScientistHasSuccessionLeaf : Bool
round6EveryScientistHasSuccessionLeaf = true

round6ScienceAdjacencyCreatesCommonCause : Bool
round6ScienceAdjacencyCreatesCommonCause = false

round6InstitutionContinuityPaysExactCapabilityTransfer : Bool
round6InstitutionContinuityPaysExactCapabilityTransfer = false

round6MultipleManifestationsCreateIndependentReplication : Bool
round6MultipleManifestationsCreateIndependentReplication = false
