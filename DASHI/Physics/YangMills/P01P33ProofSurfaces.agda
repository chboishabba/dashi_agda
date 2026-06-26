module DASHI.Physics.YangMills.P01P33ProofSurfaces where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)
open import DASHI.Physics.YangMills.ProofTargetSurface

treePathEdgesExistSurface : ProofTargetSurface
treePathEdgesExistSurface =
  mkProofTargetSurface
    "treePathEdgesExist"
    "Diestel graph theory; wrapped in DASHI.Physics.YangMills.YMSupportGraphDistance"
    "For any finite connected support graph and any vertices u,v, there exists a finite edge path from u to v; in a spanning tree there is a unique simple tree path P_T(u,v)."
    "Finite connected support graph; spanning tree chosen over the same support carrier."
    "Tree paths exist and can be used as admissible support-graph paths."
    "P33 weighted diameter domination and the anisotropic diameter branch."
    "Cannot compare tree distance witnesses to graph diameter."
    standardWrapper

graphDistMinimalitySurface : ProofTargetSurface
graphDistMinimalitySurface =
  mkProofTargetSurface
    "graphDistMinimality"
    "Diestel graph theory; wrapped in DASHI.Physics.YangMills.YMSupportGraphDistance"
    "For any connected graph G, graphDist_G(u,v) is the minimum length among all edge paths from u to v, hence every admissible path length is at least graphDist_G(u,v)."
    "Connected support graph; admissible support path between u and v."
    "Every chosen tree/support path dominates the graph distance."
    "P33 weighted diameter domination."
    "Cannot derive diameter lower bounds from chosen path representatives."
    standardWrapper

treePathBoundedByEdgeCountSurface : ProofTargetSurface
treePathBoundedByEdgeCountSurface =
  mkProofTargetSurface
    "treePathBoundedByEdgeCount"
    "Diestel graph theory; wrapped in DASHI.Physics.YangMills.YMSupportGraphDistance"
    "For any spanning tree T of a connected support graph and any u,v, the unique tree path P_T(u,v) has length bounded by the global tree edge count; for a diameter-realising pair it remains an admissible graph path."
    "Finite connected support graph; spanning tree T on the same vertex set."
    "The tree path is a controlled admissible witness in the diameter comparison chain."
    "P33 weighted diameter domination."
    "Cannot route the tree witness through the support-graph interface cleanly."
    standardWrapper

kappaStrictlyPositiveSurface : ProofTargetSurface
kappaStrictlyPositiveSurface =
  mkProofTargetSurface
    "kappaStrictlyPositive"
    "Balaban CMP 95, Proposition 1.2; Eriksson 2602.0069 §3.1"
    "The Balaban tree-distance decay constant κ satisfies κ > 0."
    "Balaban multiscale decay setup."
    "Exponential tree-distance weights are genuinely decaying."
    "P09 entropy-vs-decay arithmetic, P33 anisotropic domination."
    "Decay weights may be non-decaying, invalidating KP margins."
    paperImport

kappaNormalisedToOneSurface : ProofTargetSurface
kappaNormalisedToOneSurface =
  mkProofTargetSurface
    "kappaNormalisedToOne"
    "DASHI A2 convention; Eriksson §12.1 normalisation surface"
    "Under the DASHI A2 norm convention, the weighted tree-distance decay is rescaled so that κ = 1 without changing the inequalities consumed downstream."
    "Convention-level renormalisation of the polymer norm."
    "The effective single-link decay weight can be compared against the explicit 0.9271 margin."
    "P33 margin calculation and anisotropic diameter branch."
    "The explicit numerical margin cannot be stated in DASHI-normalised form."
    standardWrapper

polymerAnimalCountingBoundSurface : ProofTargetSurface
polymerAnimalCountingBoundSurface =
  mkProofTargetSurface
    "ImportedPolymerAnimalCountingBound"
    "Eriksson 2602.0041, Lemma 5.6"
    "The number of connected rooted polymers of diameter/size n is bounded by an exponential counting function of the form #A_n ≤ C_ani · a^n."
    "Polymer support geometry in the Step V regime."
    "Rooted polymer entropy is exponentially bounded."
    "P07 KP summability and P23 terminal KP."
    "The polymer shell sum cannot be shown finite."
    paperImport

kPSummabilityBoundSurface : ProofTargetSurface
kPSummabilityBoundSurface =
  mkProofTargetSurface
    "ImportedKPSummabilityBound"
    "Derived DASHI arithmetic surface from P06 plus KP bookkeeping / Eriksson 2602.0041"
    "The polymer counting rate and activity decay imply a Kotecky-Preiss summability bound of the required Step V form."
    "P06 counting bound; Dashi arithmetic constants; Step V weighted decay profile."
    "The local polymer shell sum is uniformly finite."
    "Step V certificate and P23 terminal KP."
    "Step V cannot be assembled from entropy control."
    auditTested

pZeroPositiveSurface : ProofTargetSurface
pZeroPositiveSurface =
  mkProofTargetSurface
    "pZeroPositive"
    "Balaban CMP 122, equation (1.89)"
    "The large-field base activity/probability term p₀(g_k) is strictly positive."
    "Balaban large-field regime with β ≥ β₀."
    "Large-field suppression has a positive base exponent."
    "P09 entropy-vs-decay arithmetic, P11 absorption, P12 DLR-LSI branch."
    "Absorption and decay estimates lose their positive baseline."
    paperImport

entropyBeatenByFullDecaySurface : ProofTargetSurface
entropyBeatenByFullDecaySurface =
  mkProofTargetSurface
    "entropyBeatenByFullDecay"
    "DASHI arithmetic closure from β ≥ β₀ and the imported decay constants"
    "The combined entropy constant satisfies the Step V smallness inequality C_entropy · exp(-alpha_decay) < 1 in the exact DASHI arithmetic form."
    "P04 κ > 0, P05 κ = 1 convention, P08 p₀(g_k) > 0, explicit Step V constants."
    "Polymer entropy is dominated by full decay."
    "P23 terminal KP and polymer diameter entropy control."
    "The shell series may diverge even with counting bounds."
    auditTested

largeFieldActivityBoundSurface : ProofTargetSurface
largeFieldActivityBoundSurface =
  mkProofTargetSurface
    "ImportedLargeFieldActivityBound"
    "Eriksson 2602.0069, Theorem 8.5; Balaban CMP 122, equation (1.100)"
    "Large-field polymer activities satisfy a uniform suppression estimate of the form |z_large(X)| ≤ C exp(-c · Phi_k(X)) or the source-equivalent tree-distance decay bound."
    "Balaban large-field decomposition and admissible activity norms."
    "Large-field contributions are exponentially suppressed."
    "Step V certificate and P23 terminal KP."
    "The large-field branch of Step V cannot close."
    paperImport

absorptionConditionSurface : ProofTargetSurface
absorptionConditionSurface =
  mkProofTargetSurface
    "ImportedAbsorptionCondition"
    "Eriksson 2602.0056 §7"
    "The corrected large-field absorption condition holds in the source form replacing the invalid cStarGreaterThanOne gate, equivalently the product C* · p₀(g_k) dominates the bad factors."
    "P08 positivity of p₀(g_k); asymptotically free regime."
    "Entropy and defect factors can be absorbed in the large-field sum."
    "Large-field suppression, Step V, and DLR-LSI entry."
    "The large-field tail may overwhelm the decay budget."
    paperImport

dLRLSIFromPolymerDecaySurface : ProofTargetSurface
dLRLSIFromPolymerDecaySurface =
  mkProofTargetSurface
    "ImportedDLRLSIFromPolymerDecay"
    "Eriksson 2602.0052, Lemma 6.3"
    "Polymer decay together with p₀(g_k) > 0 implies the DLR-LSI smallness condition δ_k < α_blk / 4."
    "Step V terminal decay input and positive base activity."
    "The DLR-LSI hypothesis is available."
    "P14 DLR-LSI theorem and OS4 cluster property."
    "The DLR-LSI branch cannot start."
    paperImport

crossScaleBoundSurface : ProofTargetSurface
crossScaleBoundSurface =
  mkProofTargetSurface
    "ImportedCrossScaleBound"
    "Eriksson 2602.0052, Lemma 5.7"
    "Cross-scale influence terms satisfy the required summable bound across RG scales."
    "DLR-LSI setup and source cross-scale decomposition."
    "The influence tail is summable."
    "P14 DLR-LSI theorem."
    "Uniform DLR-LSI cannot be propagated across scales."
    paperImport

dLRLSITheoremSurface : ProofTargetSurface
dLRLSITheoremSurface =
  mkProofTargetSurface
    "ImportedDLRLSITheorem"
    "Eriksson 2602.0052, Theorem 7.1"
    "The DLR specification satisfies a uniform logarithmic Sobolev inequality, implying Dobrushin-Shlosman complete analyticity and exponential clustering."
    "P12 smallness condition and P13 cross-scale control."
    "The lattice Gibbs specification has uniform LSI/clustering control."
    "OS4 cluster property and the mass-gap route."
    "The OS4 branch remains unsupported."
    paperImport

latticeSpectralGapSurface : ProofTargetSurface
latticeSpectralGapSurface =
  mkProofTargetSurface
    "ImportedLatticeSpectralGap"
    "Eriksson 2602.0052, Corollary 7.3"
    "The DLR-LSI route yields a positive lattice-level spectral gap Δ_latt ≥ m(β,Nc,d) > 0."
    "P14 DLR-LSI theorem."
    "A fixed-lattice positive gap is available."
    "Mass-gap bridge and fixed-lattice gap lane."
    "No positive lattice gap enters the continuum route."
    paperImport

assumptionA2FromKPCertificateSurface : ProofTargetSurface
assumptionA2FromKPCertificateSurface =
  mkProofTargetSurface
    "ImportedAssumptionA2FromKPCertificate"
    "Eriksson 2602.0072, Assumption A2 discharged by the terminal KP certificate"
    "The terminal all-diameter KP certificate implies the per-link oscillation profile required by Assumption A2."
    "P23 terminal KP certificate and its diameter-decay hypotheses."
    "RG irrelevance/oscillation control enters the Cauchy lane."
    "P17 B6 influence bound."
    "The RG-Cauchy branch cannot consume Step V."
    auditTested

b6InfluenceBoundSurface : ProofTargetSurface
b6InfluenceBoundSurface =
  mkProofTargetSurface
    "ImportedB6InfluenceBound"
    "Eriksson 2602.0072, Theorem 1.3"
    "The Efron-Stein/B6 influence seminorm is bounded by the A2 oscillation profile with summable scale decay."
    "P16 A2 oscillation control."
    "Blocked observable influences decay at the required rate."
    "P18 RG-Cauchy summability."
    "The RG increments cannot be shown summable."
    paperImport

rGCauchySummabilitySurface : ProofTargetSurface
rGCauchySummabilitySurface =
  mkProofTargetSurface
    "ImportedRGCauchySummability"
    "Eriksson 2602.0072, Corollary 5.1"
    "The RG scale increments form a Cauchy sequence because the scale-to-scale differences are bounded by a summable profile."
    "P17 B6 influence control and summable scale decay."
    "Continuum Schwinger data converges along the RG lane."
    "Continuum limit construction and uniqueness."
    "No continuum-ready Cauchy sequence is available."
    paperImport

couplingControlSurface : ProofTargetSurface
couplingControlSurface =
  mkProofTargetSurface
    "ImportedCouplingControlProof"
    "Eriksson 2602.0088, Proposition 4.1"
    "The running coupling stays in the source-specified asymptotically free regime with the bounds needed downstream."
    "RG flow in the admitted asymptotically free window."
    "Coupling control is available uniformly along the lane."
    "Continuum stability and P21 anisotropy coefficient bound."
    "Continuum scaling and anisotropy estimates lose their coupling control input."
    paperImport

anisotropicSubspaceClassificationSurface : ProofTargetSurface
anisotropicSubspaceClassificationSurface =
  mkProofTargetSurface
    "AnisotropicSubspaceClassificationTheorem"
    "Eriksson 2602.0087, Theorem 3.6"
    "The W4-scalar gauge-invariant anisotropic quotient space in classical dimension 6 is one-dimensional."
    "Representation-theoretic operator classification."
    "The anisotropic obstruction is reduced to a single generator."
    "P29 Symanzik decomposition and P32 triangular lock."
    "O(4) restoration lacks a precise anisotropic target."
    paperImport

anisotropyCoeffQuadraticBoundSurface : ProofTargetSurface
anisotropyCoeffQuadraticBoundSurface =
  mkProofTargetSurface
    "AnisotropyCoeffQuadraticBound"
    "Eriksson 2602.0087, Theorem 5.4"
    "The coefficient of the anisotropic breaking operator is quadratically small in the lattice spacing profile."
    "P19 coupling control and the source analyticity hypotheses."
    "The anisotropic defect is O(a_k^2)."
    "P30 OS1 Euclidean covariance."
    "The Ward-identity defect cannot be driven to zero."
    paperImport

insertionIntegrabilityBoundSurface : ProofTargetSurface
insertionIntegrabilityBoundSurface =
  mkProofTargetSurface
    "InsertionIntegrabilityBound"
    "Eriksson 2602.0087, Theorem 6.6"
    "The anisotropic insertion observable obeys the uniform integrability bound required to pass to the continuum Ward identity."
    "OS4 clustering input and UV polymer control."
    "Ward-identity insertion terms are uniformly integrable."
    "P30 OS1 Euclidean covariance."
    "The Ward-identity limit cannot be justified."
    paperImport

terminalKPBoundVerifiedSurface : ProofTargetSurface
terminalKPBoundVerifiedSurface =
  mkProofTargetSurface
    "TerminalKPBoundVerified"
    "Eriksson 2602.0091, Theorems 1.1 and 1.2"
    "Combining diameter domination, polymer counting, large-field suppression, and absorption yields the final KP convergence bound uniformly over the relevant scales."
    "P06-P11 and P33."
    "The terminal Step V KP bound is available."
    "allDiameterKPCertificate and the RG/DLR-LSI lanes."
    "The multiscale polymer expansion is still blocked at Step V."
    paperImport

assemblyMapCompleteSurface : ProofTargetSurface
assemblyMapCompleteSurface =
  mkProofTargetSurface
    "AssemblyMapComplete"
    "Eriksson 2602.0091, Theorem 1.3"
    "The terminal KP certificate maps into the exact assumptions consumed by the RG-Cauchy and DLR-LSI lanes."
    "P23 terminal KP together with the source dependency graph."
    "Step V output is wired to A2, polymer decay, and downstream lane inputs."
    "RG-lane consumption and DLR-LSI entry."
    "Terminal KP may exist but remain unusable by downstream gates."
    auditTested

uniformLSIFixedLatticeSurface : ProofTargetSurface
uniformLSIFixedLatticeSurface =
  mkProofTargetSurface
    "UniformLSIFixedLattice"
    "Eriksson 2602.0089, Theorem A"
    "For each finite lattice/volume in the admitted regime, the Gibbs measure satisfies an LSI with constants independent of volume."
    "Fixed-lattice admissible regime."
    "A volume-uniform LSI is available at fixed lattice spacing."
    "P26 fixed-lattice mass gap and P27 thermodynamic limit."
    "The fixed-lattice endpoint lacks a uniform functional inequality."
    paperImport

volumeUniformMassGapFixedLatticeSurface : ProofTargetSurface
volumeUniformMassGapFixedLatticeSurface =
  mkProofTargetSurface
    "VolumeUniformMassGapFixedLattice"
    "Eriksson 2602.0089, Theorem B"
    "The fixed-lattice mass gap lower bound is uniform in volume."
    "P25 uniform fixed-lattice LSI."
    "A positive fixed-lattice gap survives the thermodynamic limit."
    "Thermodynamic-limit and continuum mass-gap transfer."
    "The fixed-lattice gap may collapse with growing volume."
    paperImport

thermodynamicLimitUniqueSurface : ProofTargetSurface
thermodynamicLimitUniqueSurface =
  mkProofTargetSurface
    "ThermodynamicLimitUnique"
    "Eriksson 2602.0089, Theorem C"
    "Finite-volume Gibbs/Schwinger distributions converge to a unique infinite-volume thermodynamic limit independent of the admitted boundary conditions."
    "P25 uniform LSI and P26 volume-uniform gap."
    "A unique infinite-volume Schwinger state exists."
    "Continuum construction and the OS/Wightman endpoint."
    "The infinite-volume state may depend on volume sequence or boundary data."
    paperImport

rotationalWardIdentitySurface : ProofTargetSurface
rotationalWardIdentitySurface =
  mkProofTargetSurface
    "ImportedRotationalWardIdentity"
    "Eriksson 2602.0092, Proposition 3.2"
    "The lattice Schwinger functions satisfy the rotational Ward identity with a Jacobian-free infinitesimal rotation acting on test functions and plaquette positions, plus an O(η^2) remainder."
    "Lattice Wilson-action setting; no change of integration variables."
    "Rotational symmetry breaking is expressed as a controlled insertion identity."
    "P30 OS1 Euclidean covariance."
    "There is no starting Ward identity for O(4) restoration."
    paperImport

symanzikBreakingDecompositionSurface : ProofTargetSurface
symanzikBreakingDecompositionSurface =
  mkProofTargetSurface
    "ImportedSymanzikBreakingDecomposition"
    "Eriksson 2602.0092, Proposition 3.4"
    "The lattice breaking term decomposes into the anisotropic operator, an O(4)-invariant piece, and higher-order remainders in the exact source form."
    "P20 anisotropic classification."
    "The Ward-identity defect splits into the exact terms needed for cancellation and decay."
    "P30 OS1 Euclidean covariance."
    "Ward-identity control cannot isolate the anisotropic contribution."
    paperImport

oS1EuclideanCovarianceSurface : ProofTargetSurface
oS1EuclideanCovarianceSurface =
  mkProofTargetSurface
    "ImportedOS1EuclideanCovariance"
    "Eriksson 2602.0092, Theorem 4.2 and Corollary 4.3"
    "Combining the Ward identity, Symanzik decomposition, anisotropy decay, insertion integrability, and the triangular lock yields L_{μν} S_n = 0 in S'(R^{4n}), equivalently O(4) covariance."
    "P21, P22, P28, P29, P32."
    "OS1 Euclidean covariance is available."
    "OS1 and Wightman reconstruction."
    "The continuum Schwinger functions may retain anisotropic breaking."
    paperImport

wightmanReconstructionWithMassGapSurface : ProofTargetSurface
wightmanReconstructionWithMassGapSurface =
  mkProofTargetSurface
    "ImportedWightmanReconstructionWithMassGap"
    "Eriksson 2602.0092, Theorem 1.1 and §5"
    "Given OS0-OS4, OS1 Euclidean covariance, reflection positivity, clustering, nontriviality, and the source mass-gap hypotheses, one obtains a Wightman QFT with positive physical mass gap."
    "OS0-OS4, O(4) covariance, reflection positivity, clustering, nontriviality, and the source mass-gap transfer hypotheses."
    "A Wightman theory with positive mass gap is reconstructed at the source-intake level."
    "Terminal mathematical sink of the YM lane."
    "There is no continuum YM endpoint with a physical mass gap."
    paperImport

triangularMixingPreventiveLockSurface : ProofTargetSurface
triangularMixingPreventiveLockSurface =
  mkProofTargetSurface
    "TriangularMixingPreventiveLock"
    "Eriksson 2602.0096, Theorem 8.5 and Corollary 8.6"
    "The mixing map from the anisotropic d=6 sector has no d=4 anisotropic sink; any image lies in the O(4)-invariant d=4 sector."
    "P20 anisotropic subspace classification."
    "The a^2 × a^-2 anisotropic residue attack is structurally blocked."
    "P30 OS1 Euclidean covariance."
    "A surviving d=4 anisotropic obstruction could remain in the continuum limit."
    paperImport

fieldRegularitySourceEllipticitySurface : ProofTargetSurface
fieldRegularitySourceEllipticitySurface =
  mkProofTargetSurface
    "FieldRegularitySourceEllipticity"
    "Balaban/Eriksson small-field regularity; source-side κ-normalised link-ellipticity witness"
    "For every scale k, polymer X, and admissible support link e, one has w_k(e) ≥ m_link ≥ 1."
    "Small-field regularity input for support-link weights; κ-normalised Step V regime."
    "A source-side uniform link-ellipticity witness is available."
    "P33 composite link-positivity surface."
    "Without source ellipticity, the internal diameter domination bridge cannot be justified."
    paperImport

fieldRegularityInternalDiameterDominationSurface : ProofTargetSurface
fieldRegularityInternalDiameterDominationSurface =
  mkProofTargetSurface
    "FieldRegularityInternalDiameterDomination"
    "DASHI low-risk graph/arithmetic bridge; P01-P03 finite graph control and anisotropic diameter compatibility"
    "The source ellipticity margin is carried through the graph/arithmetic bridge into weighted diameter domination."
    "P01-P03 graph path control; P04-P05 κ normalisation; arithmetic diameter bridge."
    "Weighted diameter dominates ordinary diameter at the internal surface."
    "P33 composite link-positivity surface."
    "Without the diameter bridge, the source ellipticity witness does not reach Step V."
    proved

fieldRegularityImpliesSingleLinkPositivitySurface : ProofTargetSurface
fieldRegularityImpliesSingleLinkPositivitySurface =
  mkProofTargetSurface
    "FieldRegularityImpliesSingleLinkPositivity"
    "Balaban/Eriksson small-field regularity plus DASHI A2 normalisation; composite of source ellipticity and internal diameter domination"
    "For every scale k, polymer X, and admissible support link e, one has w_k(e) ≥ m_link ≥ 1, hence d_k^w(X) ≥ diam_k(X) and exp(-κ d_k^w(X)) ≤ exp(-κ diam_k(X))."
    "Small-field regularity input; source ellipticity witness; internal diameter domination bridge; P01-P05 graph/normalisation infrastructure."
    "Weighted tree-distance dominates ordinary diameter decay with DASHI margin 1 · 0.9271 < 1."
    "Anisotropic diameter branch, Step V certificate, and P23 terminal KP."
    "The weighted Balaban decay cannot be compared to the ordinary diameter decay used by Step V."
    paperImport

record P01P33ProofBundle : Set where
  field
    p01 : ProofTargetSurface
    p02 : ProofTargetSurface
    p03 : ProofTargetSurface
    p04 : ProofTargetSurface
    p05 : ProofTargetSurface
    p06 : ProofTargetSurface
    p07 : ProofTargetSurface
    p08 : ProofTargetSurface
    p09 : ProofTargetSurface
    p10 : ProofTargetSurface
    p11 : ProofTargetSurface
    p12 : ProofTargetSurface
    p13 : ProofTargetSurface
    p14 : ProofTargetSurface
    p15 : ProofTargetSurface
    p16 : ProofTargetSurface
    p17 : ProofTargetSurface
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
    p31 : ProofTargetSurface
    p32 : ProofTargetSurface
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
  ; p07 = kPSummabilityBoundSurface
  ; p08 = pZeroPositiveSurface
  ; p09 = entropyBeatenByFullDecaySurface
  ; p10 = largeFieldActivityBoundSurface
  ; p11 = absorptionConditionSurface
  ; p12 = dLRLSIFromPolymerDecaySurface
  ; p13 = crossScaleBoundSurface
  ; p14 = dLRLSITheoremSurface
  ; p15 = latticeSpectralGapSurface
  ; p16 = assumptionA2FromKPCertificateSurface
  ; p17 = b6InfluenceBoundSurface
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
  ; p31 = wightmanReconstructionWithMassGapSurface
  ; p32 = triangularMixingPreventiveLockSurface
  ; p33 = fieldRegularityImpliesSingleLinkPositivitySurface
  ; noClayPromotion = refl
  }
