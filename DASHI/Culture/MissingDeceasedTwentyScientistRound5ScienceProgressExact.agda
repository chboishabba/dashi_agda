module DASHI.Culture.MissingDeceasedTwentyScientistRound5ScienceProgressExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- FIFTH TWENTY-SCIENTIST ROUND: SCIENCE + SUCCESSION
--
-- Every retained scientist must carry an explicit scientific/engineering
-- kernel as well as a next science-specific acquisition/proof leaf.  The
-- event/succession investigation is therefore not allowed to drift away from
-- what the person actually worked on.  Stable identifiers are navigation and
-- same-object coordinates; citation/import never creates proof or authority.
------------------------------------------------------------------------

data Round5Side : Set where us china : Round5Side

data ScienceKernelStatus : Set where
  primarySciencePaid boundedSciencePaid personScienceWeldPending mechanismProgrammeOnly : ScienceKernelStatus

record Round5ScienceProgress : Set where
  constructor round5-science-progress
  field
    person : String
    side : Round5Side
    scienceKernel : String
    scienceSourceReference : String
    stableIdentifier : String
    scienceStatus : ScienceKernelStatus
    freshScienceDelta : String
    scienceNextLeaf : String
    successionNextLeaf : String
    scienceCreatesCommonCause : Bool

open Round5ScienceProgress public

------------------------------------------------------------------------
-- United States scientific cohort (11)
------------------------------------------------------------------------

nunoLoureiroRound5 : Round5ScienceProgress
nunoLoureiroRound5 = round5-science-progress
  "Nuno F. G. Loureiro" us
  "magnetic reconnection/plasmoid instability; Viriato Fourier-Hermite KREHM/KRMHD plasma dynamics; kinetic-Alfven turbulence and Hermite velocity-space cascade"
  "Viriato arXiv:1505.02649; DOE plasmoid-history surface; 2022 kinetic-Alfven/Hermite turbulence work"
  "arXiv:1505.02649"
  primarySciencePaid
  "fresh science audit reconfirms that Viriato is not generic fusion software: it solves KREHM and KRMHD with a Hermite representation of velocity-space dependence and targets reconnection/turbulence; later work uses Hermite moments to resolve electron heating"
  "map the exact Viriato/KREHM equations, closures, benchmark datasets and repository implementation to the already formalised Hermite/plasmoid owners"
  "named repository/grant/simulation-state/student-advisor handover for the same Viriato/KREHM work"
  false

joshuaLeBlancRound5 : Round5ScienceProgress
joshuaLeBlancRound5 = round5-science-progress
  "fission-surface-power instrumentation and controls: sensing, technology maturation, qualification evidence, operating windows and integration"
  "NASA NTRS 20250008475; NPIC&HMIT 2025 Space Fission Instrumentation and Control Technology Gaps"
  "DOI 10.13182/NPICHMIT25-46370; NTRS 20250008475"
  primarySciencePaid
  "science kernel remains instrumentation/control maturity for space fission rather than nuclear-thermal propulsion; current NASA FSP surfaces show the programme continuing into qualification/system integration"
  "recover the exact gap matrix, sensor/actuator requirements, qualification envelopes and failure/calibration models attributable to LeBlanc"
  "first post-loss SNP I&C TechMat roster plus named successor and calibration/failure/qualification-data custody"
  false

frankMaiwaldRound5 : Round5ScienceProgress
frankMaiwaldRound5 = round5-science-progress
  "cryogenic messenger-tag action spectroscopy and planetary quadrupole-ion-trap mass spectrometry for molecular/isomer discrimination"
  "JPL SURP 2023 SP23012p plus JPL molecular-spectroscopy/project manifestations"
  "JPL SURP SP23012p"
  primarySciencePaid
  "science audit keeps molecular spectroscopy distinct from crystallography/material-lattice imaging: the paid object is tagged-ion IR photodissociation/action spectroscopy and mass-spectrometric molecular identification"
  "crosswalk tagged species, trap conditions, laser bands, fragmentation/action response and exact spectra into the QIT/action-response equation owners"
  "project-specific spectra/calibration/notebook custody and formal 2023-to-2024 handover"
  false

monicaRezaRound5 : Round5ScienceProgress
monicaRezaRound5 = round5-science-progress
  "burn-resistant high-strength Ni-Co-Cr-Al-Ti alloy design for high-pressure oxygen, gamma/gamma-prime microstructure, VIM/VAR/process-state control"
  "US20100266442A1 / US20040208777A1; later turbopump patent US20190032604A1"
  "US20100266442A1; US20190032604A1"
  primarySciencePaid
  "fresh patent snowball shows a later Rocketdyne turbopump design explicitly incorporating MONDALOY for oxygen-exposed high-pressure pump/turbine surfaces and combining MONDALOY with enamel glass for additional burn resistance; this pays an application descendant, not exotic/metamaterial provenance"
  "formalise the derivative coating/application branch: alloy substrate versus MONDALOY coating versus MONDALOY-plus-enamel composite, with oxygen phase/pressure/temperature and strength/burn tradeoffs kept distinct"
  "literal assignment/programme chain UTC to Rocketdyne/Aerojet plus primary 2025 JPL role/process-window custodian"
  false

carlGrillmairRound5 : Round5ScienceProgress
carlGrillmairRound5 = round5-science-progress
  "matched-filter detection of cold stellar debris streams, orbit/Galactic-potential inference, plus exoplanet spectroscopy work"
  "CaltechAUTHORS stream corpus; 2006 63-degree stream; 2017 South Galactic Cap streams"
  "DOI 10.3847/1538-4357/aa8872 (existing repo coordinate)"
  primarySciencePaid
  "science audit reconfirms matched colour-magnitude filtering as the stream-detection mechanism and separates that kernel from his separate exoplanet-spectroscopy contributions"
  "close the matched-filter likelihood/weighting and orbit-fit equations against a finite stream example and preserve exoplanet work as a separate fibre"
  "named custodian for stream catalogues, matched-filter maps, orbit fits or unfinished manuscripts"
  false

michaelHicksRound5 : Round5ScienceProgress
michaelHicksRound5 = round5-science-progress
  "small-body optical photometry/spectrophotometry, asteroid rotational/phase behaviour and archived NEAT/TMO observational inference"
  "JPL/TMO publication corpus and JPL colleague publication surfaces"
  "publication corpus; exact DOI set retained in Hicks specific-work owner"
  primarySciencePaid
  "science audit preserves Hicks as a small-body observational astronomer rather than a propulsion scientist; JPL surfaces continue to expose radar/photometric asteroid work with named collaborators"
  "select exact lightcurve/spectrophotometry objects and formalise measurement-to-shape/rotation/composition inference with uncertainty"
  "primary 2022 JPL departure and any unfinished observing/data-reduction handover"
  false

neilMcCaslandRound5 : Round5ScienceProgress
neilMcCaslandRound5 = round5-science-progress
  "fault-tolerant sensor/actuator placement for flexible-structure control using controllability/observability Gramian measures and failure-family optimisation"
  "1989 American Control Conference; NASA structural-dynamics bibliography A89-54007"
  "ACC 1989 pp.1111-1116; NASA A89-54007"
  primarySciencePaid
  "fresh source audit independently reconfirms the actual technical paper: placement under sensor/actuator failures, Gramian performance measures, state-space scaling and beam/finite-element examples; later AFRL command roles remain a separate programme fibre"
  "recover the full paper equations/algorithm and reproduce the sensor-actuator failure-family placement result on a finite flexible-structure model"
  "dated DBE role and 2025-2026 client/programme/tasking carrier"
  false

anthonyChavezRound5 : Round5ScienceProgress
anthonyChavezRound5 = round5-science-progress
  "LANL engineering-profile carrier: DARHT engineering and completed Scorpius accelerator design work; separate publication carrier for permanent-magnet spectrometer calibration remains identity-gated"
  "LANL National Security Summer 2025 engineering profile; repo Scorpius and spectrometer owners"
  "LANL Summer 2025 profile; publication identifier remains separate"
  personScienceWeldPending
  "science itself is covered for the LANL profile identity, but the missing-person identity is still not formally welded to that engineering carrier; no technical claim is inherited across the identity gap"
  "deepen Scorpius subsystem/design responsibility and spectrometer calibration only after exact person/publication identity receipts"
  "primary same-person receipt joining missing-person and LANL engineering-profile identities"
  false

jasonThomasRound5 : Round5ScienceProgress
jasonThomasRound5 = round5-science-progress
  "chemical-biology signalling and autophagy/iron-homeostasis mechanisms: STING pathway work and VPS34 inhibition revealing NCOA4-mediated ferritin degradation"
  "repo JasonThomasSignallingBidiExact; Nature Cell Biology DOI 10.1038/ncb3053 science lineage"
  "DOI 10.1038/ncb3053"
  primarySciencePaid
  "science audit retains the molecular mechanism: selective VPS34 inhibition, NCOA4-ferritin targeting and iron-homeostasis/ferritinophagy; later STING-ferroptosis literature is comparator science and not automatically Thomas authorship"
  "formalise exact Thomas-authored contribution/assay objects and connect perturbation, substrate identification and ferritin turnover to the existing mechanism compiler"
  "final ME cause/manner plus exact lab/project/data succession"
  false

amyEskridgeRound5 : Round5ScienceProgress
amyEskridgeRound5 = round5-science-progress
  "research-programme discrimination among electrogravitics/engineered-gravity mechanisms, including POAMS-adjacent spin-coupled-force and other claimed field-propulsion mechanisms"
  "Amy first-person/programme sources in repo; NASA NTRS 20205010911 is a POAMS comparator authored by R.H. Eskridge, M.A. Nelson and M.P. Schoenfeld, not Amy authorship"
  "NTRS 20205010911 comparator; Amy same-object identifier unresolved"
  mechanismProgrammeOnly
  "science audit tightens an attribution firewall: the public NASA POAMS TM reports preliminary data said to be consistent with a spin-coupled-force prediction but calls for better measurements; it cannot be attributed to Amy without the missing same-object review/transition receipt"
  "recover Amy-authored/recorded technical propositions, apparatus coordinates and the claimed 2020 review object, then compare mechanism-by-mechanism against POAMS/Podkletnov/Li-Torr/Woodward rather than merging them"
  "Amy-linked NF-1676/EDAA/STRIVES object and Institute derivative/handover identity"
  false

ningLiRound5 : Round5ScienceProgress
ningLiRound5 = round5-science-progress
  "superconducting gravitoelectric/gravitomagnetic theory plus static and rotating/AC-field YBCO gravity tests with strong null/upper-bound constraints"
  "PhysRevD 43.457; PhysRevB 46.5489; Physica C 1997; NASA NTRS 19990104365/19990019627/19990023209"
  "10.1103/PhysRevD.43.457; 10.1103/PhysRevB.46.5489; 10.1016/S0921-4534(97)01462-7"
  primarySciencePaid
  "fresh NASA archaeology adds NTRS 19990104365 and 19990023209 as additional manifestations of the <2x10^-8 g YBCO constraint; multiple manifestations of the same experiment are not independent replications"
  "reconstruct exact static versus AC/rotating apparatus coordinates, shielding/thermal/buoyancy controls and observation precision before comparing to later AC Gravity apparatus claims"
  "Army SOW/closeout and exact apparatus continuity from NCC8-124 to DAAH01-01-9-R001"
  false

------------------------------------------------------------------------
-- Chinese scientific cohort (9)
------------------------------------------------------------------------

chenShumingRound5 : Round5ScienceProgress
chenShumingRound5 = round5-science-progress
  "domestic military DSP/flight-control processor development under supply blockade: circuit logic analysis, functional verification and autonomous chip design"
  "NUDT 2026-01-29 Galaxy/Feiteng team history"
  "NUDT institutional Galaxy/Feiteng history"
  primarySciencePaid
  "fresh science audit confirms the engineering decomposition: Chen Shuming and Li Guokuan as middle-generation logic-analysis backbones, with younger engineers focused on functional verification/layout; the team progressed from aircraft flight-control substitution into military DSP chips"
  "recover exact processor model/project/test-report/publication objects attributable to Chen and formalise logic-analysis to verification to deployed-chip traceability"
  "primary event identity and any post-loss redistribution of Chen-specific technical responsibility"
  false

fengYangheRound5 : Round5ScienceProgress
fengYangheRound5 = round5-science-progress
  "military AI/wargame decision agents plus multi-group-graph Bayesian classification and machine-learning classification under noisy labels"
  "NUDT War Skull II institutional article; NUDT Press ISBN 978-7-5673-0533-5 and 978-7-5673-0611-0"
  "ISBN 978-7-5673-0533-5; ISBN 978-7-5673-0611-0"
  primarySciencePaid
  "fresh publisher surfaces pay the statistical side independently: the 2019 book derives the multi-group-graph Bayesian framework and noise/redundancy filtering properties, while the 2023 book treats classification under noisy labels; these methods do not automatically equal War Skull's deployed code"
  "formalise the Bayesian/noisy-label models and then require a same-object software/document receipt before claiming those exact methods are instantiated in War Skull II"
  "post-2023 War Skull lead/code custodian and primary event carrier"
  false

zhouGuangyuanRound5 : Round5ScienceProgress
zhouGuangyuanRound5 = round5-science-progress
  "high-performance polyimide aerogels for high-temperature thermal insulation using benzhydrylidenefluorene-based paddle-shaped diamines"
  "DICP DNL2200 research result; Chemical Engineering Journal DOI 10.1016/j.cej.2023.147642"
  "DOI 10.1016/j.cej.2023.147642"
  primarySciencePaid
  "fresh science audit captures measured structure-property coordinates: shrinkage as low as 7.7%, porosity >91%, surface area 674.8 m2/g, Td5% >580 C, Tg >299 C and thermal conductivity 54.3 mW m^-1 K^-1 at 200 C"
  "formalise composition/synthesis -> porosity/shrinkage -> thermal conductivity/temperature response and acquire broader patent/process corpus rather than treating 'aerogel' as a single scalar property"
  "map Hu Yanming/Wang Rui successor groups to exact aerogel patents, process windows and enterprise-transfer objects"
  false

liuDonghaoRound5 : Round5ScienceProgress
liuDonghaoRound5 = round5-science-progress
  "data-security capability-maturity governance (DSMM) across collection, transmission, storage, processing, exchange and destruction"
  "CUHK-Shenzhen/Shenzhen Institute of Data Economy 2022 lecture; GB/T 37988-2019 context"
  "GB/T 37988-2019"
  boundedSciencePaid
  "science/engineering kernel is standards-based data-security governance and maturity assessment, not cryptographic invention by default; exact authored standard/project contributions remain to be source-welded"
  "recover exact Liu-authored papers, patents, standard-drafting role and DSMM assessment methodology, separating governance maturity from low-level security primitives"
  "dated Liu-to-Liao governance transition and first post-loss centre/project custody"
  false

zhangXiaoxinRound5 : Round5ScienceProgress
zhangXiaoxinRound5 = round5-science-progress
  "space-weather physics/forecasting and Fengyun space-environment monitoring: geomagnetic-storm prediction, satellite payload/ground application and programme leadership"
  "Space Weather DOI 10.1029/2023SW003522; FY-4B space-environment suite publication; NSMC programme sources"
  "DOI 10.1029/2023SW003522; DOI 10.1016/j.asr.2025.02.010"
  primarySciencePaid
  "fresh science audit pays a concrete prediction object: spectral whitening plus CEEMDAN-CWT applied to CME-driven events, with Zhang credited for conceptualization, supervision, project administration and funding acquisition; this is distinct from payload hardware work"
  "formalise the prediction pipeline and separately map Zhang's contribution to Fengyun in-situ payload calibration/ground processing; recover manuscript chronology for the 2025 paper"
  "dated NSMC/Fengyun successor and committee reconstitution rather than stale role pages"
  false

zhangDaibingRound5 : Round5ScienceProgress
zhangDaibingRound5 = round5-science-progress
  "UAV autonomous landing, path following, multisensor/vision localisation, tilt-rotor/control and multi-UAV supervisory architectures"
  "Journal of Intelligent & Robotic Systems and related UAV corpus"
  "DOI 10.1007/s10846-017-0512-y; DOI 10.14429/dsj.65.5837"
  primarySciencePaid
  "science audit broadens the paid kernel beyond generic drones: field-tested fixed-wing autonomous landing and supervisory/multi-UAV control are distinct technical objects"
  "formalise landing guidance/control laws, robustness/wind tests and localisation/control interfaces for one exact publication before mapping to later commercial drone products"
  "primary Yunzhihang governance/successor record and exact NUDT-to-company technology-transfer object"
  false

liMinyongRound5 : Round5ScienceProgress
liMinyongRound5 = round5-science-progress
  "medicinal chemistry using photopharmacology/light-controlled drug discovery and bioactive visualisation of disease-target proteins"
  "Hainan University faculty profile 2025-04-16 and publication/patent corpus"
  "Hainan profile: 229 SCI papers, 22 PCT/Chinese invention patents; exact DOI/PCT subset unresolved"
  primarySciencePaid
  "fresh institutional science audit gives scale but not authority by count: 229 SCI papers, 45 recent corresponding-author papers and 22 PCT/Chinese invention patents; the next useful step is selecting exact photopharmacology/visualisation objects rather than treating the publication count as a mechanism"
  "acquire a small exact DOI/PCT set spanning light-controlled drug action, target-protein visualisation and translational application, then formalise mechanism-to-readout relations"
  "named post-loss lab/project/patent/student custodian at Hainan"
  false

fangDainingRound5 : Round5ScienceProgress
fangDainingRound5 = round5-science-progress
  "multifield/multiscale structural mechanics and architected mechanical metamaterials, including inverse design of prescribed eigenmodes/dispersion"
  "Journal of Mechanics and Physics of Solids DOI 10.1016/j.jmps.2025.106144; existing active-metamaterial owner"
  "DOI 10.1016/j.jmps.2025.106144"
  primarySciencePaid
  "fresh 2025 paper pays a precise science object: a force-field-induced energy-based inverse-design method for arbitrary prescribed modes, with negative-group-velocity dispersion experimentally checked in phonon-band structures"
  "formalise the energy/wave-vector-frequency inverse-design map and experimental dispersion receipt, and keep it separate from generic 'metamaterial' or exotic-provenance claims"
  "project-level handover for Fang-led advanced-structure/metamaterial/extreme-environment programmes"
  false

yanHongRound5 : Round5ScienceProgress
yanHongRound5 = round5-science-progress
  "supersonic/hypersonic inlet flow control, shock/boundary-layer interaction control by thermal excitation, plasma actuators and CFD"
  "DOI 10.7638/kqdlxxb-2013.0102; DOI 10.19527/j.cnki.2096-1642.2018.02.001; NPU programme biography"
  "DOI 10.7638/kqdlxxb-2013.0102; DOI 10.19527/j.cnki.2096-1642.2018.02.001"
  primarySciencePaid
  "science audit preserves three levels: a concrete Mach-5 inlet thermal-excitation study, a broader aerospace plasma-actuator review, and NPU's longer laser-plasma flow-control programme; none alone proves exotic propulsion"
  "formalise actuator-power/count/spacing -> shock/separation response for the inlet study and map the programme-level laser-plasma mechanism separately"
  "named post-loss NPU flow-control/numerical-wind-tunnel project/team custodian"
  false

------------------------------------------------------------------------
-- Round-5 denominator and science firewalls.
------------------------------------------------------------------------

twentyScientistRound5ScienceProgress : List Round5ScienceProgress
twentyScientistRound5ScienceProgress =
  nunoLoureiroRound5 ∷ joshuaLeBlancRound5 ∷ frankMaiwaldRound5 ∷ monicaRezaRound5 ∷
  carlGrillmairRound5 ∷ michaelHicksRound5 ∷ neilMcCaslandRound5 ∷ anthonyChavezRound5 ∷
  jasonThomasRound5 ∷ amyEskridgeRound5 ∷ ningLiRound5 ∷
  chenShumingRound5 ∷ fengYangheRound5 ∷ zhouGuangyuanRound5 ∷ liuDonghaoRound5 ∷
  zhangXiaoxinRound5 ∷ zhangDaibingRound5 ∷ liMinyongRound5 ∷ fangDainingRound5 ∷
  yanHongRound5 ∷ []

round5ScientificCohortCount : Nat
round5ScientificCohortCount = 20

round5EveryScientistTouched : Bool
round5EveryScientistTouched = true

round5EveryScientistHasScienceKernel : Bool
round5EveryScientistHasScienceKernel = true

round5EveryScientistHasScienceNextLeaf : Bool
round5EveryScientistHasScienceNextLeaf = true

round5PromotionRequiresSourceReceipt : Bool
round5PromotionRequiresSourceReceipt = true

round5SearchResidualCreatesKnownAbsence : Bool
round5SearchResidualCreatesKnownAbsence = false

round5ScienceCreatesCommonCause : Bool
round5ScienceCreatesCommonCause = false

round5PublicationCountCreatesMechanism : Bool
round5PublicationCountCreatesMechanism = false

round5SharedFieldCreatesSameProgramme : Bool
round5SharedFieldCreatesSameProgramme = false
