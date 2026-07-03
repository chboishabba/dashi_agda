module DASHI.Physics.YangMills.P01P33ReplacementBacklog where

open import Agda.Builtin.Bool using (false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
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

-- Entropy-side queue: P06 feeds the counting surface, P06a/P06b/P06c expose
-- the non-canonical split, P07 consumes the arithmetic queue, and P09 closes
-- the explicit decay-vs-entropy margin.  The P06a2 lane now names the DFS-walk
-- sublemmas explicitly, and P06a3 carries the explicit
-- size-or-complexity-controlled-by-diameter leaf.

p06Entry : ProofReplacementEntry
p06Entry =
  mkProofReplacementEntry
    Surfaces.polymerAnimalCountingBoundSurface
    "Next local-lattice ownership target: collapse the remaining explicit size-or-complexity-by-diameter leaf and source animal-counting witness boundary into the already-exposed skeleton-plus-decoration chain encode/decode -> injectivity -> complexity by diameter -> decoration multiplicity -> bounded-degree skeleton animal counting -> P06ModelLeafDischargePackage."
    soon

p06aEntry : ProofReplacementEntry
p06aEntry =
  mkProofReplacementEntry
    Surfaces.p06aRootedConnectedSkeletonCountingSurface
    "Strengthen this bounded-degree skeleton bridge from theorem-shaped ownership into a genuine rooted connected skeleton counting proof, now that the root-ball growth, DFS-walk, and diameter-containment substeps are explicit."
    now

p06a1Entry : ProofReplacementEntry
p06a1Entry =
  mkProofReplacementEntry
    Surfaces.p06a1BoundedDegreeSupportGraphSkeletonSurface
    "Treat this as the canonical local graph-degree input below P06: if the YM support graph degree bound is formalised, this should become the reusable hypothesis carrier for the entire skeleton-counting lane."
    now

p06a2aEntry : ProofReplacementEntry
p06a2aEntry =
  mkProofReplacementEntry
    Surfaces.p06a2aBoundedDegreeRootBallGrowthSurface
    "Use this as the first internal graph-combinatorial bridge below P06: root-ball shell growth should become a genuine bounded-degree counting lemma rather than a theorem-shaped stub."
    now

p06a2Entry : ProofReplacementEntry
p06a2Entry =
  mkProofReplacementEntry
    Surfaces.p06a2RootedConnectedSkeletonSizeShellCountingSurface
    "Upgrade this from a theorem-shaped size-shell bridge to a real bounded-degree rooted connected skeleton counting proof, with the DFS-walk sublemmas under P06a2 kept explicit."
    now

p06a3aEntry : ProofReplacementEntry
p06a3aEntry =
  mkProofReplacementEntry
    Surfaces.p06a3aDiameterShellContainedInRootBallSurface
    "Make this the explicit size-to-diameter containment lemma so the remaining P06 residue is truly decoration overhead rather than hidden geometry."
    now

p06a3Entry : ProofReplacementEntry
p06a3Entry =
  mkProofReplacementEntry
    Surfaces.p06a3DiameterShellSkeletonCountingSurface
    "Use this as the local size-to-diameter shell bridge so the remaining P06 residue is the explicit size-or-complexity-controlled-by-diameter leaf rather than hidden graph counting."
    now

p06bEntry : ProofReplacementEntry
p06bEntry =
  mkProofReplacementEntry
    Surfaces.p06bDecorationMultiplicityBoundSurface
    "Keep this source-side unless the polymer decoration space and multiplicity overhead are formalised inside DASHI."
    soon

p06cEntry : ProofReplacementEntry
p06cEntry =
  mkProofReplacementEntry
    Surfaces.p06cSkeletonDecorationImpliesAnimalCountingSurface
    "Use this recombination reducer as the canonical P06 consumer boundary: skeleton counting plus decoration overhead imply the full imported counting witness consumed by the entropy queue."
    now

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
    "Promote this into the canonical local-lattice decay theorem: block-tail lower bound -> Gaussian tail suppression -> support-product localisation -> product suppression -> Phi-large coercive in diameter -> P10LargeFieldSuppressionPackage."
    soon

p11Entry : ProofReplacementEntry
p11Entry =
  mkProofReplacementEntry
    Surfaces.absorptionConditionSurface
    "Keep tied to the local-lattice route: once P08 positivity lemmas are explicit, close P11 only through the constants-close absorption package consumed by LocalLatticeAnalyticDischargePackage."
    soon

p12Entry : ProofReplacementEntry
p12Entry =
  mkProofReplacementEntry
    Surfaces.dLRLSIFromPolymerDecaySurface
    "Retain as paper import, but consume it only through the explicit StepVToDLRSmallness reducer rather than as an opaque Step V consequence."
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

dlrSmallnessAndCrossScaleToUniformLSIEntry : ProofReplacementEntry
dlrSmallnessAndCrossScaleToUniformLSIEntry =
  mkProofReplacementEntry
    Surfaces.dlrSmallnessAndCrossScaleToUniformLSIReducerSurface
    "Use this as the canonical local bridge out of the StepVToDLRSmallness handoff: keep the cross-scale theorem imported, but consume it only through the explicit uniform-LSI reducer."
    now

p16Entry : ProofReplacementEntry
p16Entry =
  mkProofReplacementEntry
    Surfaces.assumptionA2FromKPCertificateSurface
    "Treat as an RG-lane consumer of the explicit StepVToA2 reducer, not as a separate upstream theorem hunt."
    soon

a2ToB6Entry : ProofReplacementEntry
a2ToB6Entry =
  mkProofReplacementEntry
    Surfaces.a2ToB6InfluenceReducerSurface
    "Keep the source A2-to-B6 theorem explicit, but consume it only through the local StepVToA2 handoff so the B6 boundary is typed and auditable."
    now

p17Entry : ProofReplacementEntry
p17Entry =
  mkProofReplacementEntry
    Surfaces.b6InfluenceBoundSurface
    "Retain as paper import until the A2-to-B6 influence theorem is independently formalised."
    later

b6ToRGCauchyEntry : ProofReplacementEntry
b6ToRGCauchyEntry =
  mkProofReplacementEntry
    Surfaces.b6ToRGCauchyReducerSurface
    "Use this as the canonical local bridge from B6 influence control into the RG-Cauchy lane, keeping the imported summability theorem explicit but no longer architecturally opaque."
    now

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
    "This is the Step V terminal assembly queue item: compose P06-P11 and P33 explicitly, then hand off through StepVToDLRSmallness and StepVToA2 with no hidden closure jumps."
    now

p24Entry : ProofReplacementEntry
p24Entry =
  mkProofReplacementEntry
    Surfaces.assemblyMapCompleteSurface
    "Treat as the first RG bridge after Step V: expose the terminal KP outputs specifically through StepVToDLRSmallness and StepVToA2 as a single audited handoff."
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
    "Keep the source-side composite P31 surface explicit, but consume the new internal endpoint split: P31a abstract reconstruction interface, P31b YM OS-input bundle, and P31c cluster/gap-to-physical-mass-gap bridge."
    later

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
    "Keep P33 split, but make the metric-perturbation route canonical: local metric decomposition -> perturbation control -> positive background floor -> perturbation margin -> metric-to-link comparison -> diameter comparison -> P33a1AnalyticDischargePackage."
    now

p33a1Entry : ProofReplacementEntry
p33a1Entry =
  mkProofReplacementEntry
    Surfaces.p33a1SmallFieldRegularityGivesPositiveLinkWeightSurface
    "Highest-value current analytic leaf: reconstruct the small-field ellipticity lane through perturbation control and positive-link comparison before touching endpoint lemmas."
    now

p33a2Entry : ProofReplacementEntry
p33a2Entry =
  mkProofReplacementEntry
    Surfaces.p33a2DASHINormalisationRaisesLowerBoundToOneSurface
    "Treat this as a local ownership gain: once a positive lower-bound witness exists, keep the DASHI normalisation step internal and reusable."
    hold

p33a3Entry : ProofReplacementEntry
p33a3Entry =
  mkProofReplacementEntry
    Surfaces.p33a3UniformityAcrossScaleAndPolymerSurface
    "Treat this as the canonical local uniform-consumption wrapper: keep the analytic source leaf separate from the fact that DASHI uses it uniformly across k, X, and e."
    hold

p33aFullEntry : ProofReplacementEntry
p33aFullEntry =
  mkProofReplacementEntry
    Surfaces.p33aFullUniformLinkEllipticityFromSplitSurface
    "Use this as the single typed recombination point from P33a1/P33a2/P33a3 back into the exact ellipticity witness consumed by P33b and Step V."
    hold

record P01P33ReplacementBacklog : Set where
  field
    p01 : ProofReplacementEntry
    p02 : ProofReplacementEntry
    p03 : ProofReplacementEntry
    p04 : ProofReplacementEntry
    p05 : ProofReplacementEntry
    p06 : ProofReplacementEntry
    p06a : ProofReplacementEntry
    p06a1 : ProofReplacementEntry
    p06a2a : ProofReplacementEntry
    p06a2 : ProofReplacementEntry
    p06a3a : ProofReplacementEntry
    p06a3 : ProofReplacementEntry
    p06b : ProofReplacementEntry
    p06c : ProofReplacementEntry
    p07 : ProofReplacementEntry
    p08 : ProofReplacementEntry
    p09 : ProofReplacementEntry
    p10 : ProofReplacementEntry
    p11 : ProofReplacementEntry
    p12 : ProofReplacementEntry
    p13 : ProofReplacementEntry
    p14 : ProofReplacementEntry
    p15 : ProofReplacementEntry
    dlrSmallnessAndCrossScaleToUniformLSI : ProofReplacementEntry
    p16 : ProofReplacementEntry
    a2ToB6 : ProofReplacementEntry
    p17 : ProofReplacementEntry
    b6ToRGCauchy : ProofReplacementEntry
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
    p33a1 : ProofReplacementEntry
    p33a2 : ProofReplacementEntry
    p33a3 : ProofReplacementEntry
    p33aFull : ProofReplacementEntry
    p33 : ProofReplacementEntry
    backlogBoundary : String
    backlogBoundaryIsCanonical :
      backlogBoundary ≡
      "Per-lemma proof-replacement queue for P01-P33: entropy-side P06 stays canonical while P06a/P06a1/P06a2a/P06a2/P06a3a/P06a3/P06b/P06c expose the bounded-degree skeleton-counting, root-ball growth, DFS-walk sublemmas, size-shell, diameter-containment, explicit size-or-complexity-controlled-by-diameter leaf, decoration-bound, and recombination split; P07/P09 feed Step V, Step V feeds RG through explicit StepVToDLRSmallness, DLRSmallnessAndCrossScaleToUniformLSI, StepVToA2, A2ToB6, and B6ToRGCauchy reducers; the endpoint lane now exposes an internal P31a/P31b/P31c split while the composite source-side P31 sink remains explicit."
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP01P33ReplacementBacklog : P01P33ReplacementBacklog
currentP01P33ReplacementBacklog = record
  { p01 = p01Entry
  ; p02 = p02Entry
  ; p03 = p03Entry
  ; p04 = p04Entry
  ; p05 = p05Entry
  ; p06 = p06Entry
  ; p06a = p06aEntry
  ; p06a1 = p06a1Entry
  ; p06a2a = p06a2aEntry
  ; p06a2 = p06a2Entry
  ; p06a3a = p06a3aEntry
  ; p06a3 = p06a3Entry
  ; p06b = p06bEntry
  ; p06c = p06cEntry
  ; p07 = p07Entry
  ; p08 = p08Entry
  ; p09 = p09Entry
  ; p10 = p10Entry
  ; p11 = p11Entry
  ; p12 = p12Entry
  ; p13 = p13Entry
  ; p14 = p14Entry
  ; p15 = p15Entry
  ; dlrSmallnessAndCrossScaleToUniformLSI =
      dlrSmallnessAndCrossScaleToUniformLSIEntry
  ; p16 = p16Entry
  ; a2ToB6 = a2ToB6Entry
  ; p17 = p17Entry
  ; b6ToRGCauchy = b6ToRGCauchyEntry
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
  ; p33a1 = p33a1Entry
  ; p33a2 = p33a2Entry
  ; p33a3 = p33a3Entry
  ; p33aFull = p33aFullEntry
  ; p33 = p33Entry
  ; backlogBoundary =
      "Per-lemma proof-replacement queue for P01-P33: entropy-side P06 stays canonical while P06a/P06a1/P06a2a/P06a2/P06a3a/P06a3/P06b/P06c expose the bounded-degree skeleton-counting, root-ball growth, DFS-walk sublemmas, size-shell, diameter-containment, explicit size-or-complexity-controlled-by-diameter leaf, decoration-bound, and recombination split; P07/P09 feed Step V, Step V feeds RG through explicit StepVToDLRSmallness, DLRSmallnessAndCrossScaleToUniformLSI, StepVToA2, A2ToB6, and B6ToRGCauchy reducers; the endpoint lane now exposes an internal P31a/P31b/P31c split while the composite source-side P31 sink remains explicit."
  ; backlogBoundaryIsCanonical = refl
  ; noClayPromotion = refl
  }

record ActiveYMSprintFrontierEntry : Set where
  field
    entry : ProofReplacementEntry
    sprintLane : String
    rationale : String

activeYMSprintFrontierBoundary : String
activeYMSprintFrontierBoundary =
  "Top active YM frontier: prioritize P33a1/P33 analytic ownership, then the P06 bounded-degree skeleton-counting chain, then Step V assembly and explicit RG transfer reducers. Keep endpoint O(4)/Wightman source imports later and preserve no-clay-promotion."

p33a1FrontierEntry : ActiveYMSprintFrontierEntry
p33a1FrontierEntry = record
  { entry = p33a1Entry
  ; sprintLane = "Sprint A - P33 analytic ownership"
  ; rationale =
      "Highest-value current analytic leaf: make the small-field ellipticity route explicit before widening to the rest of the Step V lane."
  }

p33FrontierEntry : ActiveYMSprintFrontierEntry
p33FrontierEntry = record
  { entry = p33Entry
  ; sprintLane = "Sprint A - P33 analytic ownership"
  ; rationale =
      "Keep the P33 split canonical so the composite witness consumes the local metric/perturbation route rather than an opaque source jump."
  }

p06a1FrontierEntry : ActiveYMSprintFrontierEntry
p06a1FrontierEntry = record
  { entry = p06a1Entry
  ; sprintLane = "Sprint B - P06 entropy/counting ownership"
  ; rationale =
      "Bounded-degree support-graph structure is the reusable local input for the whole P06 skeleton-counting chain."
  }

p06a2aFrontierEntry : ActiveYMSprintFrontierEntry
p06a2aFrontierEntry = record
  { entry = p06a2aEntry
  ; sprintLane = "Sprint B - P06 entropy/counting ownership"
  ; rationale =
      "Root-ball growth is the first graph-combinatorial bridge below P06 and unblocks the remaining shell-counting leaves."
  }

p06a2FrontierEntry : ActiveYMSprintFrontierEntry
p06a2FrontierEntry = record
  { entry = p06a2Entry
  ; sprintLane = "Sprint B - P06 entropy/counting ownership"
  ; rationale =
      "This is the main rooted connected skeleton size-shell counting surface and should stop being a theorem-shaped stub."
  }

p06a3aFrontierEntry : ActiveYMSprintFrontierEntry
p06a3aFrontierEntry = record
  { entry = p06a3aEntry
  ; sprintLane = "Sprint B - P06 entropy/counting ownership"
  ; rationale =
      "Diameter-shell containment isolates the geometry needed before the final size-or-complexity leaf."
  }

p06a3FrontierEntry : ActiveYMSprintFrontierEntry
p06a3FrontierEntry = record
  { entry = p06a3Entry
  ; sprintLane = "Sprint B - P06 entropy/counting ownership"
  ; rationale =
      "This diameter-shell reduction is the last local graph-counting bridge before the residual source-side counting overhead."
  }

p06cFrontierEntry : ActiveYMSprintFrontierEntry
p06cFrontierEntry = record
  { entry = p06cEntry
  ; sprintLane = "Sprint B - P06 entropy/counting ownership"
  ; rationale =
      "Use recombination as the typed consumer boundary so P06 no longer flows into Step V as a black box."
  }

p07FrontierEntry : ActiveYMSprintFrontierEntry
p07FrontierEntry = record
  { entry = p07Entry
  ; sprintLane = "Sprint C - Step V assembly"
  ; rationale =
      "KP summability should be owned as an arithmetic queue item once the P06 and P33 local leaves are explicit."
  }

p09FrontierEntry : ActiveYMSprintFrontierEntry
p09FrontierEntry = record
  { entry = p09Entry
  ; sprintLane = "Sprint C - Step V assembly"
  ; rationale =
      "The decay-vs-entropy margin is the explicit arithmetic closure needed before terminal Step V assembly."
  }

p23FrontierEntry : ActiveYMSprintFrontierEntry
p23FrontierEntry = record
  { entry = p23Entry
  ; sprintLane = "Sprint C - Step V assembly"
  ; rationale =
      "This is the terminal Step V assembly surface and the right place to expose the composed local lattice ownership."
  }

dlrSmallnessFrontierEntry : ActiveYMSprintFrontierEntry
dlrSmallnessFrontierEntry = record
  { entry = dlrSmallnessAndCrossScaleToUniformLSIEntry
  ; sprintLane = "Sprint D - RG handoff cleanup"
  ; rationale =
      "The DLR smallness handoff should be the canonical typed bridge from Step V into the fixed-lattice LSI lane."
  }

a2ToB6FrontierEntry : ActiveYMSprintFrontierEntry
a2ToB6FrontierEntry = record
  { entry = a2ToB6Entry
  ; sprintLane = "Sprint D - RG handoff cleanup"
  ; rationale =
      "Keep the RG influence transfer explicit so the A2-to-B6 theorem is consumed through a visible local reducer."
  }

b6ToRGCauchyFrontierEntry : ActiveYMSprintFrontierEntry
b6ToRGCauchyFrontierEntry = record
  { entry = b6ToRGCauchyEntry
  ; sprintLane = "Sprint D - RG handoff cleanup"
  ; rationale =
      "This is the canonical typed bridge from B6 influence control into the RG-Cauchy lane."
  }

activeYMSprintFrontier : List ActiveYMSprintFrontierEntry
activeYMSprintFrontier =
  p33a1FrontierEntry ∷
  p33FrontierEntry ∷
  p06a1FrontierEntry ∷
  p06a2aFrontierEntry ∷
  p06a2FrontierEntry ∷
  p06a3aFrontierEntry ∷
  p06a3FrontierEntry ∷
  p06cFrontierEntry ∷
  p07FrontierEntry ∷
  p09FrontierEntry ∷
  p23FrontierEntry ∷
  dlrSmallnessFrontierEntry ∷
  a2ToB6FrontierEntry ∷
  b6ToRGCauchyFrontierEntry ∷
  []
