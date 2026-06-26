module DASHI.Physics.YangMills.P01P33ReplacementBacklog where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; [])
open import Agda.Builtin.String using (String)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface
import DASHI.Physics.YangMills.P01P33ProofSurfaces as Surfaces

data ReplacementPriority : Set where
  now : ReplacementPriority
  soon : ReplacementPriority
  later : ReplacementPriority
  hold : ReplacementPriority

priorityLabel : ReplacementPriority → String
priorityLabel now = "now"
priorityLabel soon = "soon"
priorityLabel later = "later"
priorityLabel hold = "hold"

record ProofReplacementEntry : Set where
  field
    surface : ProofTargetSurface
    replacementTarget : String
    priority : ReplacementPriority
    noClayPromotion : clayYangMillsPromoted ≡ false

currentStatus : ProofReplacementEntry → ProofStatus
currentStatus entry = ProofTargetSurface.status (ProofReplacementEntry.surface entry)

downstreamGate : ProofReplacementEntry → String
downstreamGate entry =
  ProofTargetSurface.consumingGate (ProofReplacementEntry.surface entry)

lemmaId : ProofReplacementEntry → String
lemmaId entry = ProofTargetSurface.lemmaName (ProofReplacementEntry.surface entry)

mkProofReplacementEntry :
  ProofTargetSurface →
  String →
  ReplacementPriority →
  ProofReplacementEntry
mkProofReplacementEntry surface replacementTarget priority =
  record
    { surface = surface
    ; replacementTarget = replacementTarget
    ; priority = priority
    ; noClayPromotion = refl
    }

p01Entry : ProofReplacementEntry
p01Entry =
  mkProofReplacementEntry
    Surfaces.treePathEdgesExistSurface
    "Keep as a standard wrapper now; later replace the imported tree-path witness with an internal finite connected graph path construction."
    now

p02Entry : ProofReplacementEntry
p02Entry =
  mkProofReplacementEntry
    Surfaces.graphDistMinimalitySurface
    "Keep as a standard wrapper now; later replace the imported minimality axiom with an internal shortest-path lemma for finite support graphs."
    now

p03Entry : ProofReplacementEntry
p03Entry =
  mkProofReplacementEntry
    Surfaces.treePathBoundedByEdgeCountSurface
    "Keep as a standard wrapper now; later replace the imported tree-path edge-count bound with an internal tree-cardinality lemma."
    now

p04Entry : ProofReplacementEntry
p04Entry =
  mkProofReplacementEntry
    Surfaces.kappaStrictlyPositiveSurface
    "Closed internally from the DASHI κ = 1 definition; downstream work should consume the witness-bearing arithmetic queue rather than reopening the citation layer."
    hold

p05Entry : ProofReplacementEntry
p05Entry =
  mkProofReplacementEntry
    Surfaces.kappaNormalisedToOneSurface
    "Closed internally as the explicit κ = 1 normalisation witness; only the rescaling/comparison lemma remains live."
    hold

-- Entropy-side queue: P06 feeds the counting surface, P07 consumes the
-- arithmetic queue, and P09 closes the explicit decay-vs-entropy margin.

p06Entry : ProofReplacementEntry
p06Entry =
  mkProofReplacementEntry
    Surfaces.polymerAnimalCountingBoundSurface
    "Keep the imported counting witness explicit; this is the combinatorial input that P07 and P09 consume, not a status-table placeholder."
    soon

p07Entry : ProofReplacementEntry
p07Entry =
  mkProofReplacementEntry
    Surfaces.kPSummabilityBoundSurface
    "Promote the arithmetic shell-sum closure into the explicit Step V arithmetic queue: derive it from P06 and the shared arithmetic constants."
    now

p08Entry : ProofReplacementEntry
p08Entry =
  mkProofReplacementEntry
    Surfaces.pZeroPositiveSurface
    "Retain as a paper import with exact Balaban positivity statement until the large-field baseline is reconstructed internally."
    soon

p09Entry : ProofReplacementEntry
p09Entry =
  mkProofReplacementEntry
    Surfaces.entropyBeatenByFullDecaySurface
    "Close the decay-vs-entropy inequality as an arithmetic queue item, with the explicit constants coming from the shared Step V bundle."
    now

-- Step V queue: P10/P11 remain upstream inputs, while P23/P24 are the
-- terminal KP assembly and the first RG bridge out of the Step V lane.

p10Entry : ProofReplacementEntry
p10Entry =
  mkProofReplacementEntry
    Surfaces.largeFieldActivityBoundSurface
    "Keep as a paper import while the Step V large-field branch is pinned to its downstream consumers and constants."
    soon

p11Entry : ProofReplacementEntry
p11Entry =
  mkProofReplacementEntry
    Surfaces.absorptionConditionSurface
    "Keep as a paper import while the corrected absorption wrapper remains the large-field gate for the Step V queue."
    soon

p12Entry : ProofReplacementEntry
p12Entry =
  mkProofReplacementEntry
    Surfaces.dLRLSIFromPolymerDecaySurface
    "Retain as paper import until the DLR-LSI smallness route is formalised beyond the Step V certificate."
    later

p13Entry : ProofReplacementEntry
p13Entry =
  mkProofReplacementEntry
    Surfaces.crossScaleBoundSurface
    "Retain as paper import with exact source theorem payload and influence-sum statement."
    later

p14Entry : ProofReplacementEntry
p14Entry =
  mkProofReplacementEntry
    Surfaces.dLRLSITheoremSurface
    "Retain as a paper import wrapper; later split into theorem wrapper plus explicit cluster-property consumer bridge."
    later

p15Entry : ProofReplacementEntry
p15Entry =
  mkProofReplacementEntry
    Surfaces.latticeSpectralGapSurface
    "Retain as paper import and keep the lattice/continuum distinction explicit."
    later

p16Entry : ProofReplacementEntry
p16Entry =
  mkProofReplacementEntry
    Surfaces.assumptionA2FromKPCertificateSurface
    "Treat as an RG-lane consumer of the terminal KP bundle, not as a separate upstream theorem hunt."
    soon

p17Entry : ProofReplacementEntry
p17Entry =
  mkProofReplacementEntry
    Surfaces.b6InfluenceBoundSurface
    "Retain as paper import until the A2-to-B6 influence theorem is independently formalised."
    later

p18Entry : ProofReplacementEntry
p18Entry =
  mkProofReplacementEntry
    Surfaces.rGCauchySummabilitySurface
    "Retain as paper import and preserve the exact summable increment statement consumed by the continuum lane."
    later

p19Entry : ProofReplacementEntry
p19Entry =
  mkProofReplacementEntry
    Surfaces.couplingControlSurface
    "Retain as paper import with exact asymptotically free regime assumptions and running-coupling bounds."
    later

p20Entry : ProofReplacementEntry
p20Entry =
  mkProofReplacementEntry
    Surfaces.anisotropicSubspaceClassificationSurface
    "Retain as paper import unless the W4/O4 operator-classification algebra is ported internally."
    later

p21Entry : ProofReplacementEntry
p21Entry =
  mkProofReplacementEntry
    Surfaces.anisotropyCoeffQuadraticBoundSurface
    "Retain as paper import with explicit dependence on coupling control and analyticity hypotheses."
    later

p22Entry : ProofReplacementEntry
p22Entry =
  mkProofReplacementEntry
    Surfaces.insertionIntegrabilityBoundSurface
    "Retain as paper import and keep its OS4 dependence explicit."
    later

p23Entry : ProofReplacementEntry
p23Entry =
  mkProofReplacementEntry
    Surfaces.terminalKPBoundVerifiedSurface
    "This is the Step V terminal assembly queue item: compose P06-P11 and P33 explicitly, with no hidden closure jumps."
    now

p24Entry : ProofReplacementEntry
p24Entry =
  mkProofReplacementEntry
    Surfaces.assemblyMapCompleteSurface
    "Treat as the first RG bridge after Step V: expose A2, decay, and the terminal KP outputs as a single audited handoff."
    soon

p25Entry : ProofReplacementEntry
p25Entry =
  mkProofReplacementEntry
    Surfaces.uniformLSIFixedLatticeSurface
    "Retain as paper import unless the fixed-lattice LSI theorem is rebuilt internally."
    later

p26Entry : ProofReplacementEntry
p26Entry =
  mkProofReplacementEntry
    Surfaces.volumeUniformMassGapFixedLatticeSurface
    "Retain as paper import with the exact volume-uniformity claim preserved."
    later

p27Entry : ProofReplacementEntry
p27Entry =
  mkProofReplacementEntry
    Surfaces.thermodynamicLimitUniqueSurface
    "Retain as paper import and keep uniqueness and boundary-condition scope explicit."
    later

p28Entry : ProofReplacementEntry
p28Entry =
  mkProofReplacementEntry
    Surfaces.rotationalWardIdentitySurface
    "Retain as paper import with the Jacobian-free rotation action stated exactly."
    later

p29Entry : ProofReplacementEntry
p29Entry =
  mkProofReplacementEntry
    Surfaces.symanzikBreakingDecompositionSurface
    "Retain as paper import with exact splitting into anisotropic and O(4)-invariant parts."
    later

p30Entry : ProofReplacementEntry
p30Entry =
  mkProofReplacementEntry
    Surfaces.oS1EuclideanCovarianceSurface
    "Retain as paper import until the Ward-identity closure chain P20-P22, P28-P29, and P32 is reconstructed internally."
    later

p31Entry : ProofReplacementEntry
p31Entry =
  mkProofReplacementEntry
    Surfaces.wightmanReconstructionWithMassGapSurface
    "Hold. This is downstream of the OS/Wightman implementation files and is not current work in the replacement queue."
    hold

p32Entry : ProofReplacementEntry
p32Entry =
  mkProofReplacementEntry
    Surfaces.triangularMixingPreventiveLockSurface
    "Retain as paper import unless the triangular mixing algebra is formalised internally."
    later

p33Entry : ProofReplacementEntry
p33Entry =
  mkProofReplacementEntry
    Surfaces.fieldRegularityImpliesSingleLinkPositivitySurface
    "Keep P33 split: retain source ellipticity as external P33a, and strengthen the internal P33b diameter-domination bridge around that assumption."
    now

record P01P33ReplacementBacklog : Set where
  field
    p01 : ProofReplacementEntry
    p02 : ProofReplacementEntry
    p03 : ProofReplacementEntry
    p04 : ProofReplacementEntry
    p05 : ProofReplacementEntry
    p06 : ProofReplacementEntry
    p07 : ProofReplacementEntry
    p08 : ProofReplacementEntry
    p09 : ProofReplacementEntry
    p10 : ProofReplacementEntry
    p11 : ProofReplacementEntry
    p12 : ProofReplacementEntry
    p13 : ProofReplacementEntry
    p14 : ProofReplacementEntry
    p15 : ProofReplacementEntry
    p16 : ProofReplacementEntry
    p17 : ProofReplacementEntry
    p18 : ProofReplacementEntry
    p19 : ProofReplacementEntry
    p20 : ProofReplacementEntry
    p21 : ProofReplacementEntry
    p22 : ProofReplacementEntry
    p23 : ProofReplacementEntry
    p24 : ProofReplacementEntry
    p25 : ProofReplacementEntry
    p26 : ProofReplacementEntry
    p27 : ProofReplacementEntry
    p28 : ProofReplacementEntry
    p29 : ProofReplacementEntry
    p30 : ProofReplacementEntry
    p31 : ProofReplacementEntry
    p32 : ProofReplacementEntry
    p33 : ProofReplacementEntry
    backlogBoundary : String
    backlogBoundaryIsCanonical :
      backlogBoundary ≡
      "Per-lemma proof-replacement queue for P01-P33: entropy-side P06/P07/P09 feed Step V, Step V feeds RG, and P31 is hold because the OS/Wightman implementation files are not current work."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP01P33ReplacementBacklog : P01P33ReplacementBacklog
currentP01P33ReplacementBacklog = record
  { p01 = p01Entry
  ; p02 = p02Entry
  ; p03 = p03Entry
  ; p04 = p04Entry
  ; p05 = p05Entry
  ; p06 = p06Entry
  ; p07 = p07Entry
  ; p08 = p08Entry
  ; p09 = p09Entry
  ; p10 = p10Entry
  ; p11 = p11Entry
  ; p12 = p12Entry
  ; p13 = p13Entry
  ; p14 = p14Entry
  ; p15 = p15Entry
  ; p16 = p16Entry
  ; p17 = p17Entry
  ; p18 = p18Entry
  ; p19 = p19Entry
  ; p20 = p20Entry
  ; p21 = p21Entry
  ; p22 = p22Entry
  ; p23 = p23Entry
  ; p24 = p24Entry
  ; p25 = p25Entry
  ; p26 = p26Entry
  ; p27 = p27Entry
  ; p28 = p28Entry
  ; p29 = p29Entry
  ; p30 = p30Entry
  ; p31 = p31Entry
  ; p32 = p32Entry
  ; p33 = p33Entry
  ; backlogBoundary =
      "Per-lemma proof-replacement queue for P01-P33: entropy-side P06/P07/P09 feed Step V, Step V feeds RG, and P31 is hold because the OS/Wightman implementation files are not current work."
  ; backlogBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }
