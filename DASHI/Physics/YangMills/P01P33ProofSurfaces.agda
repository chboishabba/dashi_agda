module DASHI.Physics.YangMills.P01P33ProofSurfaces where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface

open import DASHI.Physics.YangMills.YMSourceAuthoritySurface using
  ( SourceAuthorityId
  ; eriksson-2602-0041
  ; eriksson-2602-0052
  ; eriksson-2602-0056
  ; eriksson-2602-0069
  ; eriksson-2602-0072
  ; eriksson-2602-0087
  ; eriksson-2602-0088
  ; eriksson-2602-0089
  ; eriksson-2602-0091
  ; eriksson-2602-0092
  ; eriksson-2602-0096
  ; balaban-cmp-095
  ; balaban-cmp-099
  ; balaban-cmp-109
  ; balaban-cmp-116
  ; balaban-cmp-122
  ; zenodo-18799942
  ; zenodo-18800920
  ; diestel-graph-theory
  ; dashi-internal-proof
  ; unknown-authority
  ; VerificationStatus
  ; proved
  ; standardWrapper
  ; paperImport
  ; auditTested
  ; openTarget
  ; mixedReducer
  ; ClaimRole
  ; postulate-import
  ; consequence-proof
  ; convention-definition
  )

treePathEdgesExistSurface : ProofTargetSurface
treePathEdgesExistSurface =
  mkProofTargetSurfaceWithAuthority
    "treePathEdgesExist"
    "Diestel graph theory; wrapped in DASHI.Physics.YangMills.YMSupportGraphDistance"
    "For any finite connected support graph and any vertices u,v, there exists a finite edge path from u to v; in a spanning tree there is a unique simple tree path P_T(u,v)."
    "Finite connected support graph; spanning tree chosen over the same support carrier."
    "Tree paths exist and can be used as admissible support-graph paths."
    "P33 weighted diameter domination and the anisotropic diameter branch."
    "Cannot compare tree distance witnesses to graph diameter."
    standardWrapper
    diestel-graph-theory "§1.5.1" postulate-import standardWrapper

graphDistMinimalitySurface : ProofTargetSurface
graphDistMinimalitySurface =
  mkProofTargetSurfaceWithAuthority
    "graphDistMinimality"
    "Diestel graph theory; wrapped in DASHI.Physics.YangMills.YMSupportGraphDistance"
    "For any connected graph G, graphDist_G(u,v) is the minimum length among all edge paths from u to v, hence every admissible path length is at least graphDist_G(u,v)."
    "Connected support graph; admissible support path between u and v."
    "Every chosen tree/support path dominates the graph distance."
    "P33 weighted diameter domination."
    "Cannot derive diameter lower bounds from chosen path representatives."
    standardWrapper
    diestel-graph-theory "§1.5.1" postulate-import standardWrapper

treePathBoundedByEdgeCountSurface : ProofTargetSurface
treePathBoundedByEdgeCountSurface =
  mkProofTargetSurfaceWithAuthority
    "treePathBoundedByEdgeCount"
    "Diestel graph theory; wrapped in DASHI.Physics.YangMills.YMSupportGraphDistance"
    "For any spanning tree T of a connected support graph and any u,v, the unique tree path P_T(u,v) has length bounded by the global tree edge count; for a diameter-realising pair it remains an admissible graph path."
    "Finite connected support graph; spanning tree T on the same vertex set."
    "The tree path is a controlled admissible witness in the diameter comparison chain."
    "P33 weighted diameter domination."
    "Cannot route the tree witness through the support-graph interface cleanly."
    standardWrapper
    diestel-graph-theory "§1.5.1" postulate-import standardWrapper

kappaStrictlyPositiveSurface : ProofTargetSurface
kappaStrictlyPositiveSurface =
  mkProofTargetSurfaceWithAuthority
    "kappaStrictlyPositive"
    "DASHI κ-definition closure over the Balaban decay lane"
    "The DASHI-normalised tree-distance decay constant κ is definitionally 1, hence κ > 0."
    "DASHI κ = 1 convention in the Balaban multiscale decay setup."
    "Exponential tree-distance weights are genuinely decaying."
    "P09 entropy-vs-decay arithmetic, P33 anisotropic domination."
    "Decay weights may be non-decaying, invalidating KP margins."
    proved
    dashi-internal-proof "ArithmeticLemmaQueue.lemmaP04-1-kappaPositive" consequence-proof proved

kappaNormalisedToOneSurface : ProofTargetSurface
kappaNormalisedToOneSurface =
  mkProofTargetSurfaceWithAuthority
    "kappaNormalisedToOne"
    "DASHI A2 convention with explicit normalisation witness"
    "Under the DASHI A2 norm convention, the weighted tree-distance decay is normalised by the definitional equality κ = 1."
    "Convention-level renormalisation of the polymer norm."
    "The effective single-link decay weight can be compared against the explicit 0.9271 margin."
    "P33 margin calculation and anisotropic diameter branch."
    "The explicit numerical margin cannot be stated in DASHI-normalised form."
    proved
    dashi-internal-proof "ArithmeticLemmaQueue.lemmaP05-1-kappaNormalisedToOne" convention-definition proved

polymerAnimalCountingBoundSurface : ProofTargetSurface
polymerAnimalCountingBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedPolymerAnimalCountingBound"
    "Eriksson 2602.0041, Lemma 5.6"
    "P06 is a mixed reducer: DASHI owns size-shell skeleton counting and recombination; remaining leaves are reduced-skeleton complexity control, decoration multiplicity, and skeleton-decoration decomposition."
    "Polymer support geometry in the Step V regime."
    "Rooted polymer entropy is exponentially bounded."
    "P07 KP summability and P23 terminal KP."
    "The polymer shell sum cannot be shown finite."
    paperImport
    eriksson-2602-0041 "Lemma 5.6" postulate-import paperImport

p06AnimalCountingReducerSurface : ProofTargetSurface
p06AnimalCountingReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "P06AnimalCountingReducer"
    "DASHI rooted-shell adapter for the imported polymer animal counting witness"
    "The P06 counting theorem is consumed through an explicit rooted-polymer shell interface, separating the DASHI-owned combinatorial adapter from the still-imported source counting estimate."
    "ImportedPolymerAnimalCountingBound together with the local rooted-shell encoding."
    "The entropy lane no longer consumes P06 as a completely opaque theorem sink."
    "P07 KP summability and the Step V entropy queue."
    "The counting input remains architecturally opaque inside Step V."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06AnimalCountingReducer" consequence-proof proved

p06aRootedConnectedSkeletonCountingSurface : ProofTargetSurface
p06aRootedConnectedSkeletonCountingSurface =
  mkProofTargetSurfaceWithAuthority
    "P06aRootedConnectedSkeletonCounting"
    "DASHI bounded-degree support-graph bridge for rooted connected polymer skeleton counting"
    "The P06 counting theorem is split first at the support-graph level: bounded-degree rooted connected polymer skeletons are exposed through bounded-degree input, root-ball growth, size-shell counting, diameter-shell containment, and diameter-shell reduction."
    "Local rooted-shell encoding of connected support-graph skeletons together with an explicit bounded-degree parameter."
    "The graph skeleton side of the counting problem is no longer opaque and no longer jumps directly from interface to full diameter shell."
    "P06c recombination and the Step V entropy queue."
    "There is no local skeleton-level handle on the P06 counting theorem."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06aRootedConnectedSkeletonCounting" consequence-proof proved

p06a1BoundedDegreeSupportGraphSkeletonSurface : ProofTargetSurface
p06a1BoundedDegreeSupportGraphSkeletonSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a1BoundedDegreeSupportGraphSkeleton"
    "DASHI bounded-degree support-graph skeleton input below the local P06 split"
    "The graph-skeleton side of P06 is exposed as a rooted support-graph shell family together with an explicit bounded-degree parameter."
    "Local rooted-shell encoding of support-graph skeletons."
    "The bounded-degree graph input needed by skeleton counting is explicit."
    "P06a2 size-shell counting and P06a3 diameter-shell reduction."
    "Skeleton counting would still hide its graph-degree hypothesis."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06a1BoundedDegreeSupportGraphSkeleton" consequence-proof proved

p06a2aBoundedDegreeRootBallGrowthSurface : ProofTargetSurface
p06a2aBoundedDegreeRootBallGrowthSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a2aBoundedDegreeRootBallGrowth"
    "DASHI root-ball shell growth bridge below the local P06 skeleton split"
    "Before any polymer-specific counting refinement, the rooted bounded-degree shell family is exposed as a root-ball growth bound over diameter shells."
    "P06a1 bounded-degree support-graph skeleton input and the rooted shell interface."
    "The first purely graph-combinatorial growth bound below P06 is explicit."
    "P06a2 size-shell counting and P06a3 diameter-shell reduction."
    "The local P06 split would still jump directly from bounded degree to size-shell counting."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06a2aBoundedDegreeRootBallGrowth" consequence-proof proved

p06a2bConnectedSkeletonHasRootedSpanningTreeSurface : ProofTargetSurface
p06a2bConnectedSkeletonHasRootedSpanningTreeSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a2bConnectedSkeletonHasRootedSpanningTree"
    "DASHI spanning-tree leaf below the local P06 split"
    "Every rooted connected support-graph skeleton is first reduced to a rooted spanning-tree witness before any DFS walk encoding is applied."
    "P06a1 bounded-degree support-graph skeleton input."
    "The spanning-tree reduction is explicit."
    "P06a2c DFS-walk witness and P06a2d walk-count leaf."
    "The local P06 split would still skip the tree witness."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentConnectedSkeletonHasRootedSpanningTree" consequence-proof proved

p06a2cRootedTreeDFSWalkSurface : ProofTargetSurface
p06a2cRootedTreeDFSWalkSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a2cRootedTreeDFSWalk"
    "DASHI DFS-walk leaf below the local P06 split"
    "Each rooted spanning tree is consumed through a depth-first traversal witness of length linear in the tree size."
    "P06a2b rooted spanning-tree witness."
    "The DFS walk encoding is explicit."
    "P06a2d bounded-degree walk count and P06a2e walk cover."
    "The local P06 split would still hide the traversal witness."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentRootedTreeDFSWalk" consequence-proof proved

p06a2dBoundedDegreeWalkCountSurface : ProofTargetSurface
p06a2dBoundedDegreeWalkCountSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a2dBoundedDegreeWalkCount"
    "DASHI bounded-degree walk-count leaf below the local P06 split"
    "Bounded-degree support graphs bound the number of rooted walks of any fixed length by a simple exponential walk-count estimate."
    "P06a2c DFS-walk witness."
    "The walk-count estimate is explicit."
    "P06a2e DFS cover and P06a3 diameter-shell reduction."
    "The local P06 split would still skip the walk multiplicity bound."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentBoundedDegreeWalkCount" consequence-proof proved

p06a2eConnectedSkeletonCoveredByDFSWalkSurface : ProofTargetSurface
p06a2eConnectedSkeletonCoveredByDFSWalkSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a2eConnectedSkeletonCoveredByDFSWalk"
    "DASHI DFS-cover leaf below the local P06 split"
    "Every rooted connected skeleton is covered by the visited set of a bounded-degree DFS walk, exposing the exact counting bridge used by P06a2."
    "P06a2c DFS-walk witness and P06a2d walk-count leaf."
    "The DFS visited-set cover is explicit."
    "P06a3 size-shell reduction and P06c recombination."
    "The local P06 split would still hide the visited-set cover."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentConnectedSkeletonCoveredByDFSWalk" consequence-proof proved

p06a2RootedConnectedSkeletonSizeShellCountingSurface : ProofTargetSurface
p06a2RootedConnectedSkeletonSizeShellCountingSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a2RootedConnectedSkeletonSizeShellCounting"
    "DASHI size-shell counting bridge over bounded-degree rooted connected skeletons"
    "Bounded-degree rooted connected skeletons are counted in size-indexed shells after the DFS-walk sublemmas and before any polymer-specific decoration overhead is considered."
    "P06a1 bounded-degree support-graph skeleton input, P06a2a root-ball growth, and P06a2b/P06a2c/P06a2d/P06a2e DFS-walk leaves."
    "The size-shell bridge is explicit."
    "P06a3a diameter-shell containment and P06a3b size-or-complexity leaf."
    "Diameter-shell counting would still have no internal size-shell source."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06a2RootedConnectedSkeletonSizeShellCounting" consequence-proof proved

p06a3aDiameterShellContainedInRootBallSurface : ProofTargetSurface
p06a3aDiameterShellContainedInRootBallSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a3aDiameterShellContainedInRootBall"
    "DASHI diameter-shell containment bridge below the local P06 skeleton split"
    "Diameter-indexed rooted connected skeleton shells are first reduced to a bounded root-ball containment statement before the final diameter-shell count is consumed."
    "P06a2 size-shell counting bridge."
    "The size-to-diameter transition under P06 is explicit."
    "P06a3 diameter-shell counting and P06c recombination."
    "The local P06 split would still hide the root-ball containment step."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06a3aDiameterShellContainedInRootBall" consequence-proof proved

p06a3bReducedSkeletonCardinalityBoundSurface : ProofTargetSurface
p06a3bReducedSkeletonCardinalityBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a3bReducedSkeletonCardinalityBound"
    "DASHI size-or-complexity-by-diameter leaf below the local P06 split"
    "Bounded degree alone is not enough for exponential diameter-shell counting, so DASHI keeps the missing size-or-complexity-controlled-by-diameter statement as an explicit leaf."
    "P06a3a diameter-shell containment."
    "The size-or-complexity leaf is explicit."
    "P06a3 diameter-shell reduction and P06c recombination."
    "The local P06 split would still hide the diameter-controlled complexity gate."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentReducedSkeletonCardinalityBound" consequence-proof proved

p06a3DiameterShellSkeletonCountingSurface : ProofTargetSurface
p06a3DiameterShellSkeletonCountingSurface =
  mkProofTargetSurfaceWithAuthority
    "P06a3DiameterShellSkeletonCounting"
    "DASHI diameter-shell reduction over bounded-degree rooted connected skeletons"
    "Diameter-indexed rooted connected skeleton shells are reduced to the bounded-degree size-shell counting bridge and the explicit size-or-complexity-by-diameter leaf before the decoration leaf is applied."
    "P06a2 size-shell counting bridge, P06a3a diameter-shell containment, and P06a3b size-or-complexity leaf."
    "The diameter-shell side of the graph skeleton count is explicit."
    "P06c recombination and the Step V entropy queue."
    "The local P06 split would still jump from size shells to full polymer counting."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06a3DiameterShellSkeletonCounting" consequence-proof proved

p06bDecorationMultiplicityBoundSurface : ProofTargetSurface
p06bDecorationMultiplicityBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "P06bPolymerDecorationMultiplicityBound"
    "Eriksson 2602.0041 decoration/multiplicity side-condition kept explicit below the local P06 split"
    "Any polymer-specific decoration or multiplicity overhead beyond the rooted connected support-graph skeleton is bounded in the source-side theorem shape consumed by the P06 recombination step."
    "Rooted connected skeleton shell fixed; source-side polymer decorations not yet formalised internally."
    "Decoration overhead is isolated as the only non-skeleton leaf in the local P06 split."
    "P06c recombination and the entropy queue."
    "The graph skeleton split would still hide polymer-specific multiplicity overhead."
    paperImport
    eriksson-2602-0041 "P06b decoration/multiplicity side-condition" postulate-import paperImport

p06cSkeletonDecorationImpliesAnimalCountingSurface : ProofTargetSurface
p06cSkeletonDecorationImpliesAnimalCountingSurface =
  mkProofTargetSurfaceWithAuthority
    "P06cSkeletonDecorationImpliesAnimalCounting"
    "DASHI recombination reducer over local P06a shells and explicit P06b decoration overhead"
    "The full imported P06 counting theorem is consumed via a split interface: rooted connected skeleton shells plus an explicit decoration-multiplicity leaf."
    "P06a rooted skeleton interface, P06b decoration bound, and the imported full counting witness."
    "The entropy lane consumes P06 through a skeleton-plus-decoration reducer rather than a monolithic counting import."
    "P06AnimalCountingReducer, P07 KP summability, and the Step V entropy queue."
    "The new P06 split would not yet reach the existing entropy reducer."
    proved
    dashi-internal-proof "BalabanPolymerDiameterEntropy.currentP06cSkeletonDecorationImpliesAnimalCounting" consequence-proof proved

kPSummabilityBoundSurface : ProofTargetSurface
kPSummabilityBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedKPSummabilityBound"
    "DASHI conditional reducer consumed by StepVMarginFromP33bAndArithmetic"
    "Animal counting plus activity decay plus the entropy margin AB < 1 imply the Kotecky-Preiss summability bound needed in Step V."
    "P06 counting bound; nonnegative counting/activity rates; entropy margin AB < 1."
    "The local polymer shell sum is uniformly finite."
    "Step V certificate and P23 terminal KP."
    "Step V cannot be assembled from entropy control."
    auditTested
    eriksson-2602-0041 "" postulate-import auditTested

pZeroPositiveSurface : ProofTargetSurface
pZeroPositiveSurface =
  mkProofTargetSurfaceWithAuthority
    "pZeroPositive"
    "Balaban CMP 122, equation (1.89)"
    "The large-field base activity/probability term p₀(g_k) is strictly positive."
    "Balaban large-field regime with β ≥ β₀."
    "Large-field suppression has a positive base exponent."
    "P09 entropy-vs-decay arithmetic, P11 absorption, P12 DLR-LSI branch."
    "Absorption and decay estimates lose their positive baseline."
    paperImport
    eriksson-2602-0041 "Theorem 2.1" postulate-import paperImport

entropyBeatenByFullDecaySurface : ProofTargetSurface
entropyBeatenByFullDecaySurface =
  mkProofTargetSurfaceWithAuthority
    "entropyBeatenByFullDecay"
    "DASHI arithmetic closure consumed by StepVMarginFromP33bAndArithmetic"
    "The full Step V margin chain closes internally: 4q = 9271/10000 < 1 and every nonnegative C_diam <= 1 satisfies C_diam * 4q < 1."
    "P04 κ > 0, P05 κ = 1 convention, explicit fourQ arithmetic, and the diameter constant bound C_diam <= 1."
    "Polymer entropy is dominated by full decay."
    "P23 terminal KP and polymer diameter entropy control."
    "The shell series may diverge even with counting bounds."
    auditTested
    eriksson-2602-0041 "" postulate-import auditTested

largeFieldActivityBoundSurface : ProofTargetSurface
largeFieldActivityBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedLargeFieldActivityBound"
    "Eriksson 2602.0069, Theorem 8.5; Balaban CMP 122, equation (1.100)"
    "Large-field polymer activities satisfy a uniform suppression estimate of the form |z_large(X)| ≤ C exp(-c · Phi_k(X)) or the source-equivalent tree-distance decay bound."
    "Balaban large-field decomposition and admissible activity norms."
    "Large-field contributions are exponentially suppressed."
    "Step V certificate and P23 terminal KP."
    "The large-field branch of Step V cannot close."
    paperImport
    eriksson-2602-0069 "Theorem 8.5" postulate-import paperImport

absorptionConditionSurface : ProofTargetSurface
absorptionConditionSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedAbsorptionCondition"
    "Eriksson 2602.0056 §7"
    "The corrected large-field absorption condition holds in the source form replacing the invalid cStarGreaterThanOne gate, equivalently the product C* · p₀(g_k) dominates the bad factors."
    "P08 positivity of p₀(g_k); asymptotically free regime."
    "Entropy and defect factors can be absorbed in the large-field sum."
    "Large-field suppression, Step V, and DLR-LSI entry."
    "The large-field tail may overwhelm the decay budget."
    paperImport
    eriksson-2602-0056 "§7" postulate-import paperImport

dLRLSIFromPolymerDecaySurface : ProofTargetSurface
dLRLSIFromPolymerDecaySurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedDLRLSIFromPolymerDecay"
    "Eriksson 2602.0052, Lemma 6.3"
    "Polymer decay together with p₀(g_k) > 0 implies the DLR-LSI smallness condition δ_k < α_blk / 4."
    "StepVToDLRSmallness, positive base activity, and the source DLR comparison constants."
    "The DLR-LSI hypothesis is available."
    "P14 DLR-LSI theorem and OS4 cluster property."
    "The DLR-LSI branch cannot start."
    paperImport
    eriksson-2602-0052 "Lemma 6.3" postulate-import paperImport

stepVToDLRSmallnessReducerSurface : ProofTargetSurface
stepVToDLRSmallnessReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "StepVToDLRSmallness"
    "DASHI mixed reducer factoring Step V through an explicit polymer-decay certificate before the DLR smallness inequality"
    "The Step V spatial KP certificate is re-expressed as a polymer-decay certificate and then consumed by the δ_k < α_blk DLR-smallness interface."
    "StepVMarginFromP33bAndArithmetic and the imported DLR smallness inequality shape."
    "The Step V output is exposed in the exact form consumed by the DLR-LSI lane."
    "RG/DLR-LSI handoff below P12."
    "The DLR-LSI branch remains opaque at the Step V boundary."
    proved
    dashi-internal-proof "StepVAssemblyLemmaQueue.currentStepVToDLRSmallness" consequence-proof proved

dlrSmallnessAndCrossScaleToUniformLSIReducerSurface : ProofTargetSurface
dlrSmallnessAndCrossScaleToUniformLSIReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "DLRSmallnessAndCrossScaleToUniformLSI"
    "DASHI mixed reducer joining the local DLR-smallness handoff with explicit cross-scale summability before the imported uniform LSI theorem"
    "The Step V supplied DLR-smallness witness and the cross-scale summability witness are consumed together as the exact bridge into the uniform LSI lane."
    "StepVToDLRSmallness together with the imported cross-scale influence summability shape."
    "The DLR-LSI lane is no longer opaque between Step V and the uniform LSI theorem."
    "RG/DLR-LSI handoff below P13-P14."
    "The DLR lane would still jump directly from Step V to a paper theorem."
    proved
    dashi-internal-proof "StepVAssemblyLemmaQueue.currentDLRSmallnessAndCrossScaleToUniformLSI" consequence-proof proved

crossScaleBoundSurface : ProofTargetSurface
crossScaleBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedCrossScaleBound"
    "Eriksson 2602.0052, Lemma 5.7"
    "Cross-scale influence terms satisfy the required summable bound across RG scales."
    "DLR-LSI setup and source cross-scale decomposition."
    "The influence tail is summable."
    "P14 DLR-LSI theorem."
    "Uniform DLR-LSI cannot be propagated across scales."
    paperImport
    eriksson-2602-0052 "Lemma 5.7" postulate-import paperImport

dLRLSITheoremSurface : ProofTargetSurface
dLRLSITheoremSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedDLRLSITheorem"
    "Eriksson 2602.0052, Theorem 7.1"
    "The DLR specification satisfies a uniform logarithmic Sobolev inequality, implying Dobrushin-Shlosman complete analyticity and exponential clustering."
    "P12 smallness condition and P13 cross-scale control."
    "The lattice Gibbs specification has uniform LSI/clustering control."
    "OS4 cluster property and the mass-gap route."
    "The OS4 branch remains unsupported."
    paperImport
    eriksson-2602-0052 "Theorem 7.1" postulate-import paperImport

latticeSpectralGapSurface : ProofTargetSurface
latticeSpectralGapSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedLatticeSpectralGap"
    "Eriksson 2602.0052, Corollary 7.3"
    "The DLR-LSI route yields a positive lattice-level spectral gap Δ_latt ≥ m(β,Nc,d) > 0."
    "P14 DLR-LSI theorem."
    "A fixed-lattice positive gap is available."
    "Mass-gap bridge and fixed-lattice gap lane."
    "No positive lattice gap enters the continuum route."
    paperImport
    eriksson-2602-0052 "Corollary 7.3" postulate-import paperImport

assumptionA2FromKPCertificateSurface : ProofTargetSurface
assumptionA2FromKPCertificateSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedAssumptionA2FromKPCertificate"
    "Eriksson 2602.0072, Assumption A2 discharged by the terminal KP certificate"
    "The terminal all-diameter KP certificate implies the per-link oscillation profile required by Assumption A2."
    "StepVToA2 together with the terminal KP diameter-decay hypotheses."
    "RG irrelevance/oscillation control enters the Cauchy lane."
    "P17 B6 influence bound."
    "The RG-Cauchy branch cannot consume Step V."
    auditTested
    eriksson-2602-0072 "Assumption A2" postulate-import auditTested

stepVToA2ReducerSurface : ProofTargetSurface
stepVToA2ReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "StepVToA2"
    "DASHI mixed reducer exposing the Step V spatial KP certificate as the exact A2 input for the RG-Cauchy lane"
    "The Step V spatial KP certificate is consumed as the per-link oscillation/A2 witness used by the RG-Cauchy branch."
    "StepVMarginFromP33bAndArithmetic and the imported A2 theorem shape."
    "The Step V output is exposed in the exact form consumed by the A2/B6 route."
    "RG-Cauchy handoff below P16."
    "The RG-Cauchy branch remains opaque at the Step V boundary."
    proved
    dashi-internal-proof "StepVAssemblyLemmaQueue.currentStepVToA2" consequence-proof proved

a2ToB6InfluenceReducerSurface : ProofTargetSurface
a2ToB6InfluenceReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "A2ToB6Influence"
    "DASHI mixed reducer consuming the local Step V to A2 handoff before the imported B6 theorem"
    "The A2 oscillation witness supplied by Step V is consumed in the exact form required by the B6 influence-bound theorem."
    "StepVToA2 and the imported A2-to-B6 theorem shape."
    "The RG-Cauchy lane has an explicit A2 to B6 boundary."
    "RG-Cauchy handoff below P17."
    "The B6 theorem would still be consumed through an opaque A2 jump."
    proved
    dashi-internal-proof "StepVAssemblyLemmaQueue.currentA2ToB6Influence" consequence-proof proved

b6InfluenceBoundSurface : ProofTargetSurface
b6InfluenceBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedB6InfluenceBound"
    "Eriksson 2602.0072, Theorem 1.3"
    "The Efron-Stein/B6 influence seminorm is bounded by the A2 oscillation profile with summable scale decay."
    "P16 A2 oscillation control, locally exposed through StepVToA2."
    "Blocked observable influences decay at the required rate."
    "P18 RG-Cauchy summability."
    "The RG increments cannot be shown summable."
    paperImport
    eriksson-2602-0072 "Theorem 1.3" postulate-import paperImport

rGCauchySummabilitySurface : ProofTargetSurface
rGCauchySummabilitySurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedRGCauchySummability"
    "Eriksson 2602.0072, Corollary 5.1"
    "The RG scale increments form a Cauchy sequence because the scale-to-scale differences are bounded by a summable profile."
    "P17 B6 influence control, the StepVToA2 handoff, and summable scale decay."
    "Continuum Schwinger data converges along the RG lane."
    "Continuum limit construction and uniqueness."
    "No continuum-ready Cauchy sequence is available."
    paperImport
    eriksson-2602-0072 "Corollary 5.1" postulate-import paperImport

b6ToRGCauchyReducerSurface : ProofTargetSurface
b6ToRGCauchyReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "B6ToRGCauchy"
    "DASHI mixed reducer consuming the explicit B6 profile before the imported RG-Cauchy conclusion"
    "Once the B6 influence profile is exposed, the RG-Cauchy lane consumes it as the exact summable-increment witness."
    "A2ToB6Influence and the imported B6-to-Cauchy theorem shape."
    "The RG-Cauchy lane no longer jumps directly from A2 to the final Cauchy statement."
    "RG-Cauchy handoff below P18."
    "The continuum convergence lane would still hide the B6 consumption boundary."
    proved
    dashi-internal-proof "StepVAssemblyLemmaQueue.currentB6ToRGCauchy" consequence-proof proved

couplingControlSurface : ProofTargetSurface
couplingControlSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedCouplingControlProof"
    "Eriksson 2602.0088, Proposition 4.1"
    "The running coupling stays in the source-specified asymptotically free regime with the bounds needed downstream."
    "RG flow in the admitted asymptotically free window."
    "Coupling control is available uniformly along the lane."
    "Continuum stability and P21 anisotropy coefficient bound."
    "Continuum scaling and anisotropy estimates lose their coupling control input."
    paperImport
    eriksson-2602-0088 "Proposition 4.1" postulate-import paperImport

anisotropicSubspaceClassificationSurface : ProofTargetSurface
anisotropicSubspaceClassificationSurface =
  mkProofTargetSurfaceWithAuthority
    "AnisotropicSubspaceClassificationTheorem"
    "Eriksson 2602.0087, Theorem 3.6"
    "The W4-scalar gauge-invariant anisotropic quotient space in classical dimension 6 is one-dimensional."
    "Representation-theoretic operator classification."
    "The anisotropic obstruction is reduced to a single generator."
    "P29 Symanzik decomposition and P32 triangular lock."
    "O(4) restoration lacks a precise anisotropic target."
    paperImport
    eriksson-2602-0087 "Theorem 3.6" postulate-import paperImport

anisotropyCoeffQuadraticBoundSurface : ProofTargetSurface
anisotropyCoeffQuadraticBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "AnisotropyCoeffQuadraticBound"
    "Eriksson 2602.0087, Theorem 5.4"
    "The coefficient of the anisotropic breaking operator is quadratically small in the lattice spacing profile."
    "P19 coupling control and the source analyticity hypotheses."
    "The anisotropic defect is O(a_k^2)."
    "P30 OS1 Euclidean covariance."
    "The Ward-identity defect cannot be driven to zero."
    paperImport
    eriksson-2602-0087 "Theorem 5.4" postulate-import paperImport

insertionIntegrabilityBoundSurface : ProofTargetSurface
insertionIntegrabilityBoundSurface =
  mkProofTargetSurfaceWithAuthority
    "InsertionIntegrabilityBound"
    "Eriksson 2602.0087, Theorem 6.6"
    "The anisotropic insertion observable obeys the uniform integrability bound required to pass to the continuum Ward identity."
    "OS4 clustering input and UV polymer control."
    "Ward-identity insertion terms are uniformly integrable."
    "P30 OS1 Euclidean covariance."
    "The Ward-identity limit cannot be justified."
    paperImport
    eriksson-2602-0087 "Theorem 6.6" postulate-import paperImport

terminalKPBoundVerifiedSurface : ProofTargetSurface
terminalKPBoundVerifiedSurface =
  mkProofTargetSurfaceWithAuthority
    "TerminalKPBoundVerified"
    "Eriksson 2602.0091, Theorems 1.1 and 1.2"
    "Combining diameter domination, polymer counting, large-field suppression, and absorption yields the final KP convergence bound uniformly over the relevant scales."
    "P06-P11 and P33."
    "The terminal Step V KP bound is available."
    "allDiameterKPCertificate plus the explicit StepVToDLRSmallness and StepVToA2 handoff reducers."
    "The multiscale polymer expansion is still blocked at Step V."
    paperImport
    eriksson-2602-0091 "Theorems 1.1 + 1.2" postulate-import paperImport

assemblyMapCompleteSurface : ProofTargetSurface
assemblyMapCompleteSurface =
  mkProofTargetSurfaceWithAuthority
    "AssemblyMapComplete"
    "Eriksson 2602.0091, Theorem 1.3"
    "The terminal KP certificate maps into the exact assumptions consumed by the RG-Cauchy and DLR-LSI lanes."
    "P23 terminal KP together with the source dependency graph and the local StepVToDLRSmallness / StepVToA2 reducers."
    "Step V output is wired to A2, polymer decay, and downstream lane inputs through explicit mixed reducers."
    "RG-lane consumption and DLR-LSI entry."
    "Terminal KP may exist but remain unusable by downstream gates."
    auditTested
    eriksson-2602-0091 "Theorem 1.3" postulate-import auditTested

uniformLSIFixedLatticeSurface : ProofTargetSurface
uniformLSIFixedLatticeSurface =
  mkProofTargetSurfaceWithAuthority
    "UniformLSIFixedLattice"
    "Eriksson 2602.0089, Theorem A"
    "For each finite lattice/volume in the admitted regime, the Gibbs measure satisfies an LSI with constants independent of volume."
    "Fixed-lattice admissible regime."
    "A volume-uniform LSI is available at fixed lattice spacing."
    "P26 fixed-lattice mass gap and P27 thermodynamic limit."
    "The fixed-lattice endpoint lacks a uniform functional inequality."
    paperImport
    eriksson-2602-0089 "Theorem A" postulate-import paperImport

volumeUniformMassGapFixedLatticeSurface : ProofTargetSurface
volumeUniformMassGapFixedLatticeSurface =
  mkProofTargetSurfaceWithAuthority
    "VolumeUniformMassGapFixedLattice"
    "Eriksson 2602.0089, Theorem B"
    "The fixed-lattice mass gap lower bound is uniform in volume."
    "P25 uniform fixed-lattice LSI."
    "A positive fixed-lattice gap survives the thermodynamic limit."
    "Thermodynamic-limit and continuum mass-gap transfer."
    "The fixed-lattice gap may collapse with growing volume."
    paperImport
    eriksson-2602-0089 "Theorem B" postulate-import paperImport

thermodynamicLimitUniqueSurface : ProofTargetSurface
thermodynamicLimitUniqueSurface =
  mkProofTargetSurfaceWithAuthority
    "ThermodynamicLimitUnique"
    "Eriksson 2602.0089, Theorem C"
    "Finite-volume Gibbs/Schwinger distributions converge to a unique infinite-volume thermodynamic limit independent of the admitted boundary conditions."
    "P25 uniform LSI and P26 volume-uniform gap."
    "A unique infinite-volume Schwinger state exists."
    "Continuum construction and the OS/Wightman endpoint."
    "The infinite-volume state may depend on volume sequence or boundary data."
    paperImport
    eriksson-2602-0089 "Theorem C" postulate-import paperImport

rotationalWardIdentitySurface : ProofTargetSurface
rotationalWardIdentitySurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedRotationalWardIdentity"
    "Eriksson 2602.0092, Proposition 3.2"
    "The lattice Schwinger functions satisfy the rotational Ward identity with a Jacobian-free infinitesimal rotation acting on test functions and plaquette positions, plus an O(η^2) remainder."
    "Lattice Wilson-action setting; no change of integration variables."
    "Rotational symmetry breaking is expressed as a controlled insertion identity."
    "P30 OS1 Euclidean covariance."
    "There is no starting Ward identity for O(4) restoration."
    paperImport
    eriksson-2602-0092 "Proposition 3.2" postulate-import paperImport

symanzikBreakingDecompositionSurface : ProofTargetSurface
symanzikBreakingDecompositionSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedSymanzikBreakingDecomposition"
    "Eriksson 2602.0092, Proposition 3.4"
    "The lattice breaking term decomposes into the anisotropic operator, an O(4)-invariant piece, and higher-order remainders in the exact source form."
    "P20 anisotropic classification."
    "The Ward-identity defect splits into the exact terms needed for cancellation and decay."
    "P30 OS1 Euclidean covariance."
    "Ward-identity control cannot isolate the anisotropic contribution."
    paperImport
    eriksson-2602-0092 "Proposition 3.4" postulate-import paperImport

oS1EuclideanCovarianceSurface : ProofTargetSurface
oS1EuclideanCovarianceSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedOS1EuclideanCovariance"
    "Eriksson 2602.0092, Theorem 4.2 and Corollary 4.3"
    "Combining the Ward identity, Symanzik decomposition, anisotropy decay, insertion integrability, and the triangular lock yields L_{μν} S_n = 0 in S'(R^{4n}), equivalently O(4) covariance."
    "P21, P22, P28, P29, P32."
    "OS1 Euclidean covariance is available."
    "OS1 and Wightman reconstruction."
    "The continuum Schwinger functions may retain anisotropic breaking."
    paperImport
    eriksson-2602-0092 "Theorem 4.2 + Corollary 4.3" postulate-import paperImport

wightmanAbstractReconstructionReducerSurface : ProofTargetSurface
wightmanAbstractReconstructionReducerSurface =
  mkProofTargetSurfaceWithAuthority
    "P31aAbstractReconstructionReducer"
    "DASHI-owned Wightman reconstruction reducer/interface over the local endpoint queue"
    "Assuming OS0-OS4, DASHI exposes a reusable abstract reconstruction interface that packages the Wightman endpoint route without claiming an internal constructive proof of the full endpoint."
    "OS0-OS4 source-intake surfaces and the endpoint queue structure."
    "The route has an internal reducer/interface boundary."
    "P31b YM OS-input bundle and P31c physical mass-gap bridge."
    "The OS dataflow cannot be assembled into a single proof-target interface."
    proved
    dashi-internal-proof "WightmanEndpointLemmaQueue.lemmaW-1-OSReconstruction / currentWightmanEndpointBundle" consequence-proof proved

ymSatisfiesOSInputsSurface : ProofTargetSurface
ymSatisfiesOSInputsSurface =
  mkProofTargetSurfaceWithAuthority
    "P31bYMSatisfiesOSInputs"
    "DASHI mixed OS-input bundle over Eriksson 2602.0088, 2602.0052, and 2602.0092"
    "The Yang-Mills route supplies OS0-OS4 and OS1 in the bundled theorem shape consumed by the abstract reconstruction interface."
    "Tier-1 OS inputs, the DLR-LSI/cluster route for OS4, and O(4) covariance for OS1."
    "The YM route satisfies the endpoint OS-input requirements."
    "P31a abstract reconstruction interface and P31c physical mass-gap bridge."
    "The endpoint lane cannot consume the Yang-Mills route as a single OS-input bundle."
    proved
    dashi-internal-proof "WightmanEndpointLemmaQueue.currentP31bYMSatisfiesOSInputs" consequence-proof proved

clusterGapToPhysicalMassGapSurface : ProofTargetSurface
clusterGapToPhysicalMassGapSurface =
  mkProofTargetSurfaceWithAuthority
    "P31cClusterGapToPhysicalMassGap"
    "DASHI mixed bridge over W.3 cluster-to-gap transfer and W.5 physical-scale identification"
    "OS4 clustering yields an abstract positive mass gap, and the source-side physical-scale identification anchors that gap to the Yang-Mills scale ΛYM."
    "OS4 cluster property, positive cN, positive ΛYM, and the source mass-scale identification route."
    "The physical mass-gap bridge is exposed explicitly."
    "Composite P31 endpoint surface."
    "The reconstructed gap remains unanchored to the physical Yang-Mills scale."
    proved
    dashi-internal-proof "WightmanEndpointLemmaQueue.currentP31cClusterGapToPhysicalMassGap" consequence-proof proved

wightmanReconstructionWithMassGapSurface : ProofTargetSurface
wightmanReconstructionWithMassGapSurface =
  mkProofTargetSurfaceWithAuthority
    "ImportedWightmanReconstructionWithMassGap"
    "Eriksson 2602.0092, Theorem 1.1 and §5"
    "Given OS0-OS4, OS1 Euclidean covariance, reflection positivity, clustering, nontriviality, and the source mass-gap hypotheses, one obtains a Wightman QFT with positive physical mass gap."
    "OS0-OS4, O(4) covariance, reflection positivity, clustering, nontriviality, and the source mass-gap transfer hypotheses."
    "A Wightman theory with positive mass gap is reconstructed at the source-intake level."
    "Terminal mathematical sink of the YM lane."
    "There is no continuum YM endpoint with a physical mass gap."
    paperImport
    eriksson-2602-0092 "Theorem 1.1 + §5" postulate-import paperImport

triangularMixingPreventiveLockSurface : ProofTargetSurface
triangularMixingPreventiveLockSurface =
  mkProofTargetSurfaceWithAuthority
    "TriangularMixingPreventiveLock"
    "Eriksson 2602.0096, Theorem 8.5 and Corollary 8.6"
    "The mixing map from the anisotropic d=6 sector has no d=4 anisotropic sink; any image lies in the O(4)-invariant d=4 sector."
    "P20 anisotropic subspace classification."
    "The a^2 × a^-2 anisotropic residue attack is structurally blocked."
    "P30 OS1 Euclidean covariance."
    "A surviving d=4 anisotropic obstruction could remain in the continuum limit."
    paperImport
    eriksson-2602-0096 "Theorem 8.5 + Corollary 8.6" postulate-import paperImport

p33aUniformLinkEllipticitySurface : ProofTargetSurface
p33aUniformLinkEllipticitySurface =
  mkProofTargetSurfaceWithAuthority
    "FieldRegularitySourceEllipticity"
    "Balaban/Eriksson small-field regularity; source-side κ-normalised link-ellipticity witness"
    "For every scale k, polymer X, and admissible support link e, one has w_k(e) ≥ m_link ≥ 1."
    "Small-field regularity input for support-link weights; κ-normalised Step V regime."
    "A source-side uniform link-ellipticity witness is available."
    "P33 composite link-positivity surface."
    "Without source ellipticity, the internal diameter domination bridge cannot be justified."
    paperImport
    eriksson-2602-0056 "regularity-axiom" postulate-import paperImport

p33a1SmallFieldRegularityGivesPositiveLinkWeightSurface : ProofTargetSurface
p33a1SmallFieldRegularityGivesPositiveLinkWeightSurface =
  mkProofTargetSurfaceWithAuthority
    "P33a1SmallFieldRegularityGivesPositiveLinkWeight"
    "Source-side analytic ellipticity leaf isolated below the local P33 split"
    "Small-field regularity gives the positive lower-bounded support-link weight statement for every admissible edge."
    "Balaban/Eriksson small-field regularity for admissible support links."
    "The genuinely analytic part of P33a is isolated as a single leaf."
    "P33a2 DASHI normalisation, P33a3 uniformity consumption, and P33b."
    "The P33a split would still hide the analytic ellipticity core."
    paperImport
    eriksson-2602-0056 "regularity-axiom" postulate-import paperImport

p33a2DASHINormalisationRaisesLowerBoundToOneSurface : ProofTargetSurface
p33a2DASHINormalisationRaisesLowerBoundToOneSurface =
  mkProofTargetSurfaceWithAuthority
    "P33a2DASHINormalisationRaisesLowerBoundToOne"
    "DASHI normalisation reducer over the imported positive link lower bound"
    "Once a strictly positive support-link lower bound exists, DASHI consumes it in the normalised convention where the minimum admissible link weight is at least one."
    "P33a1 positive lower-bounded link weight witness."
    "The normalisation part of P33a is no longer opaque."
    "P33b weighted diameter domination and Step V arithmetic."
    "The local P33 chain would still mix source ellipticity with internal rescaling."
    proved
    dashi-internal-proof "BalabanAnisotropicDiameterCompatibility.currentP33a2DASHINormalisationRaisesLowerBoundToOne" consequence-proof proved

p33a3UniformityAcrossScaleAndPolymerSurface : ProofTargetSurface
p33a3UniformityAcrossScaleAndPolymerSurface =
  mkProofTargetSurfaceWithAuthority
    "P33a3UniformityAcrossScaleAndPolymer"
    "DASHI explicit uniform-consumption wrapper over the imported positive link lower bound"
    "The support-link lower bound is consumed uniformly across scale, polymer, and admissible edge rather than as a local one-off estimate."
    "P33a1 positive lower-bounded link weight witness."
    "The uniformity consumption part of P33a is explicit."
    "P33b weighted diameter domination."
    "The P33 lane would still hide where uniformity enters."
    proved
    dashi-internal-proof "BalabanAnisotropicDiameterCompatibility.currentP33a3UniformityAcrossScaleAndPolymer" consequence-proof proved

p33aFullUniformLinkEllipticityFromSplitSurface : ProofTargetSurface
p33aFullUniformLinkEllipticityFromSplitSurface =
  mkProofTargetSurfaceWithAuthority
    "P33aFullUniformLinkEllipticityFromSplit"
    "DASHI recombination reducer over the split P33a lane"
    "The split P33a1/P33a2/P33a3 lane is recombined into the exact uniform-link-ellipticity witness consumed by the internal P33b diameter-domination theorem."
    "P33a1 analytic regularity leaf plus local P33a2 normalisation and P33a3 uniformity consumption."
    "The internal P33 chain no longer jumps from split leaves back to an opaque wrapper."
    "P33b weighted diameter domination and Step V assembly."
    "The P33 split would still lack a single typed recombination point."
    proved
    dashi-internal-proof "BalabanAnisotropicDiameterCompatibility.currentP33aFullUniformLinkEllipticityFromSplit" consequence-proof proved

p33bWeightedTreeDistanceDominatesOrdinaryDiameterSurface : ProofTargetSurface
p33bWeightedTreeDistanceDominatesOrdinaryDiameterSurface =
  mkProofTargetSurfaceWithAuthority
    "FieldRegularityInternalDiameterDomination"
    "DASHI low-risk graph/arithmetic bridge; P01-P03 finite graph control and anisotropic diameter compatibility"
    "The source ellipticity margin is carried through the graph/arithmetic bridge into weighted diameter domination."
    "P01-P03 graph path control; P04-P05 κ normalisation; arithmetic diameter bridge."
    "Weighted diameter dominates ordinary diameter at the internal surface."
    "P33 composite link-positivity surface."
    "Without the diameter bridge, the source ellipticity witness does not reach Step V."
    proved
    dashi-internal-proof "graph-consequence" consequence-proof proved

fieldRegularityImpliesSingleLinkPositivitySurface : ProofTargetSurface
fieldRegularityImpliesSingleLinkPositivitySurface =
  mkProofTargetSurfaceWithAuthority
    "FieldRegularityImpliesSingleLinkPositivity"
    "Balaban/Eriksson small-field regularity plus DASHI A2 normalisation; composite of source ellipticity and internal diameter domination"
    "For every scale k, polymer X, and admissible support link e, one has w_k(e) ≥ m_link ≥ 1, hence d_k^w(X) ≥ diam_k(X) and exp(-κ d_k^w(X)) ≤ exp(-κ diam_k(X))."
    "Small-field regularity input; source ellipticity witness; internal diameter domination bridge; P01-P05 graph/normalisation infrastructure."
    "Weighted tree-distance dominates ordinary diameter decay with DASHI margin 1 · 0.9271 < 1."
    "Anisotropic diameter branch, Step V certificate, and P23 terminal KP."
    "The weighted Balaban decay cannot be compared to the ordinary diameter decay used by Step V."
    paperImport
    unknown-authority "" postulate-import paperImport

record P01P33ProofBundle : Set where
  field
    p01 : ProofTargetSurface
    p02 : ProofTargetSurface
    p03 : ProofTargetSurface
    p04 : ProofTargetSurface
    p05 : ProofTargetSurface
    p06 : ProofTargetSurface
    p06a : ProofTargetSurface
    p06a1 : ProofTargetSurface
    p06a2a : ProofTargetSurface
    p06a2b : ProofTargetSurface
    p06a2c : ProofTargetSurface
    p06a2d : ProofTargetSurface
    p06a2e : ProofTargetSurface
    p06a2 : ProofTargetSurface
    p06a3a : ProofTargetSurface
    p06a3b : ProofTargetSurface
    p06a3 : ProofTargetSurface
    p06b : ProofTargetSurface
    p06c : ProofTargetSurface
    p06Reducer : ProofTargetSurface
    p07 : ProofTargetSurface
    p08 : ProofTargetSurface
    p09 : ProofTargetSurface
    p10 : ProofTargetSurface
    p11 : ProofTargetSurface
    stepVToDLRSmallness : ProofTargetSurface
    p12 : ProofTargetSurface
    p13 : ProofTargetSurface
    p14 : ProofTargetSurface
    p15 : ProofTargetSurface
    dlrSmallnessAndCrossScaleToUniformLSI : ProofTargetSurface
    stepVToA2 : ProofTargetSurface
    p16 : ProofTargetSurface
    a2ToB6 : ProofTargetSurface
    p17 : ProofTargetSurface
    b6ToRGCauchy : ProofTargetSurface
    p18 : ProofTargetSurface
    p19 : ProofTargetSurface
    p20 : ProofTargetSurface
    p21 : ProofTargetSurface
    p22 : ProofTargetSurface
    p23 : ProofTargetSurface
    p24 : ProofTargetSurface
    p25 : ProofTargetSurface
    p26 : ProofTargetSurface
    p27 : ProofTargetSurface
    p28 : ProofTargetSurface
    p29 : ProofTargetSurface
    p30 : ProofTargetSurface
    p31a : ProofTargetSurface
    p31b : ProofTargetSurface
    p31c : ProofTargetSurface
    p32 : ProofTargetSurface
    p33a1 : ProofTargetSurface
    p33a2 : ProofTargetSurface
    p33a3 : ProofTargetSurface
    p33aFull : ProofTargetSurface
    p33 : ProofTargetSurface
    noClayPromotion : clayYangMillsPromoted ≡ false

currentP01P33ProofBundle : P01P33ProofBundle
currentP01P33ProofBundle = record
  { p01 = treePathEdgesExistSurface
  ; p02 = graphDistMinimalitySurface
  ; p03 = treePathBoundedByEdgeCountSurface
  ; p04 = kappaStrictlyPositiveSurface
  ; p05 = kappaNormalisedToOneSurface
  ; p06 = polymerAnimalCountingBoundSurface
  ; p06a = p06aRootedConnectedSkeletonCountingSurface
  ; p06a1 = p06a1BoundedDegreeSupportGraphSkeletonSurface
  ; p06a2a = p06a2aBoundedDegreeRootBallGrowthSurface
  ; p06a2b = p06a2bConnectedSkeletonHasRootedSpanningTreeSurface
  ; p06a2c = p06a2cRootedTreeDFSWalkSurface
  ; p06a2d = p06a2dBoundedDegreeWalkCountSurface
  ; p06a2e = p06a2eConnectedSkeletonCoveredByDFSWalkSurface
  ; p06a2 = p06a2RootedConnectedSkeletonSizeShellCountingSurface
  ; p06a3a = p06a3aDiameterShellContainedInRootBallSurface
  ; p06a3b = p06a3bReducedSkeletonCardinalityBoundSurface
  ; p06a3 = p06a3DiameterShellSkeletonCountingSurface
  ; p06b = p06bDecorationMultiplicityBoundSurface
  ; p06c = p06cSkeletonDecorationImpliesAnimalCountingSurface
  ; p06Reducer = p06AnimalCountingReducerSurface
  ; p07 = kPSummabilityBoundSurface
  ; p08 = pZeroPositiveSurface
  ; p09 = entropyBeatenByFullDecaySurface
  ; p10 = largeFieldActivityBoundSurface
  ; p11 = absorptionConditionSurface
  ; stepVToDLRSmallness = stepVToDLRSmallnessReducerSurface
  ; p12 = dLRLSIFromPolymerDecaySurface
  ; p13 = crossScaleBoundSurface
  ; p14 = dLRLSITheoremSurface
  ; p15 = latticeSpectralGapSurface
  ; dlrSmallnessAndCrossScaleToUniformLSI =
      dlrSmallnessAndCrossScaleToUniformLSIReducerSurface
  ; stepVToA2 = stepVToA2ReducerSurface
  ; p16 = assumptionA2FromKPCertificateSurface
  ; a2ToB6 = a2ToB6InfluenceReducerSurface
  ; p17 = b6InfluenceBoundSurface
  ; b6ToRGCauchy = b6ToRGCauchyReducerSurface
  ; p18 = rGCauchySummabilitySurface
  ; p19 = couplingControlSurface
  ; p20 = anisotropicSubspaceClassificationSurface
  ; p21 = anisotropyCoeffQuadraticBoundSurface
  ; p22 = insertionIntegrabilityBoundSurface
  ; p23 = terminalKPBoundVerifiedSurface
  ; p24 = assemblyMapCompleteSurface
  ; p25 = uniformLSIFixedLatticeSurface
  ; p26 = volumeUniformMassGapFixedLatticeSurface
  ; p27 = thermodynamicLimitUniqueSurface
  ; p28 = rotationalWardIdentitySurface
  ; p29 = symanzikBreakingDecompositionSurface
  ; p30 = oS1EuclideanCovarianceSurface
  ; p31a = wightmanAbstractReconstructionReducerSurface
  ; p31b = ymSatisfiesOSInputsSurface
  ; p31c = clusterGapToPhysicalMassGapSurface
  ; p32 = triangularMixingPreventiveLockSurface
  ; p33a1 = p33a1SmallFieldRegularityGivesPositiveLinkWeightSurface
  ; p33a2 = p33a2DASHINormalisationRaisesLowerBoundToOneSurface
  ; p33a3 = p33a3UniformityAcrossScaleAndPolymerSurface
  ; p33aFull = p33aFullUniformLinkEllipticityFromSplitSurface
  ; p33 = fieldRegularityImpliesSingleLinkPositivitySurface
  ; noClayPromotion = refl
  }
