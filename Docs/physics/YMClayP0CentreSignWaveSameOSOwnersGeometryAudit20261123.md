# YM P0 — source-first doubled centre, signed wave phase space and pre-existing SU(N) same-H gap owners

23 November 2026. Geometric-forward source audit and exact finite SymPy 1.14 regression. NOT native Agda/Lean/CI, physical continuous-Haar RG, W3, interacting OS or Clay completion.

## Owner precedence and live checks

Checked master, YM #1536, physical CMP119/122 research donor #1444, reflection donor #1535, RH time/k C26 #1533, TOE H05 #1291 and R559 #1281. Master is one unrelated NS-roadmap commit ahead of the common PR base. No new group, Fourier, graph, gauge or positive-gap framework is needed.

Existing owners READ:
- Biology/TriadicKernelLiftQuotientExact: nine=T², four nonzero antipodal pairs, one fixed zero; hence five distinct sign-inversion orbits.
- Moonshine/Base369P2FiveOrbitOrientationGroupoidsExact: source carrier is (five inversion orbits) × (two orientation signs) = 10 labelled objects. The SAME 10 objects admit gauge-C2 sign-flip semantics with FIVE groupoid components, or retained/provenance semantics with TEN components. The carrier alone DOES NOT select which semantics apply.
- Reasoning/LeechPuncturedNineArithmeticExact, Docs/LeechLILAPrimePuncturedNineJWaveMaxCut20261101.md, Moonshine/C3FourierConjugationExact: eight punctured spatial points, eight nonconstant dual Fourier characters and the ninth constant DC mode are different types. A zero spatial centre is not automatically the Fourier zero mode.
- Core/ConsumerDescentMinimalObserverExact (FactorsThrough), ConsumerFibreRepairExact, IntersectionalNonFactorability, J analytic/jCoarse and admissible sheaf owner modules: source observer sufficiency and retention depend on the consumer, not merely cardinality.
- Physics/YangMills/SUNMatrixCarrier, SUNMatrixLieGroup, SU3MatrixInstance, compact-simple classification, original full Wilson/Haar/F19 owner: SU(N) source is richly present. SU3 is the N=3 instance of a CertifiedSUNMatrixTheory and carries an imported finite-matrix authority, not a preproved continuum measure.
- Positive-gap/same-H source owners ARE PRESENT: BalabanClayDenseCoreSpectralGapExact, BalabanOSMassGapClosure, YangMillsWilsonSameHMassGapRound552Exact, YangMillsDirectSourceOSSameHGapExact, YangMillsDirectSourceOSReconstructedSpectrumH3Exact, YangMillsStressOSSourceFirstSemigroupCoreToClosureExact, YMClayR387PhysicalSpectrumExact. They already own dense-core spectral exclusion, positive transfer-gap construction, same-Hilbert-space certificate compilation, OS reconstruction and Ward/semigroup common-core gluing. Their original physical fields (uniform real Wilson clustering, continuum measure, actual H and spectrum, stress core) are CONDITIONAL; these are real existing constructors, not necessarily fully inhabited physical SU(N) witnesses.
- YangMillsFreeGaussianMaxwellNoGapExact provides the source-type *massless* free Maxwell negative control, not a shortcut to an interacting gap.

## Why the centre occurs twice

X=F3² has 9 points. Sign inversion x→-x fixes exactly the centre 0 and pairs the other 8 points into 4 orbits. The independent ten-object oriented cover E=FiveOrbit×{+,-} assigns two labels to EVERY orbit, including the fixed centre. Its natural map p:E→X has one source point over each of the 8 nonzero x, but two distinct LABELS (0,+) and (0,-) over the SAME x=0. This is an orientation-fibre or fixed-point desingularization, NOT an intrinsic second zero of the base space.

The exact canonical Base369 groupoid owner explicitly permits TWO semantics: flip both signs as gauge arrows (π0=5), or retain both as provenance (π0=10). The geometric carrier cannot decide whether the double centre should survive into an observer/Hilbert space; source-specific dynamics or admissibility must decide.

## Exact finite 9-site -> 10-site wave geometry, local SymPy PASS

Take the periodic C3×C3 torus graph, not the non-wrapping P3×P3 graph. Its symmetric positive nearest-neighbour Laplacian L9 has eigenvalues 0 once, 3 fourfold, 6 fourfold. The Fourier DC mode is the CONSTANT all-ones vector; the spatial delta function at the centre is NOT that Fourier zero mode. The eight other dual characters give four complex-conjugate pairs.

Lift J from 9 source amplitudes to 10 oriented labels by COPYING the centre value to both. Give each nonzero site weight 1 and each centre label weight 1/2; with D=diag(weights), define P=JᵀD (AVERAGE centre labels). Then

    P J = I9;   Pi=J P;   Pi²=Pi;   rank(Pi)=9;
    ker(P)=span(b), b=e_(0,+)-e_(0,-).

The additional signed residual b is orthogonal to the lifted DC mode in the D-weighted inner product. The original nonidentity sign inversion R on E exchanges the two zero labels, has 5 even and 5 odd dimensions, and Rb=-b while R J(DC)=J(DC).

A source-typed lifted wave operator Hκ=J L9 P + κ(I10-JP) obeys TWO commuting squares

    Hκ J = J L9,
    P Hκ = L9 P,

plus D Hκ=HκᵀD (correct weighted self-adjointness) and R Hκ=Hκ R (true C2). Its spectra are exactly:
- κ=0: zero multiplicity 2; 3 multiplicity 4; 6 multiplicity 4. One extra zero-mode belongs solely to the doubled-centre retained sign fibre.
- κ=2: zero multiplicity 1; 2 multiplicity 1; 3 multiplicity 4; 6 multiplicity 4. A selected *finite model* energy 2 has been INTRODUCED as fibre stiffness. It is NOT derived from SU(N) Wilson action nor any original same-OS Hamiltonian.
- A second zero mode may be physically null/gauge (prove quotient) or a retained zero-energy excitation (prove correct sector). One may not silently identify absence of spectral modes with a unique physical vacuum.

## Reverse solve the genuine wave interpretation

The actual wave state is (displacement u, time derivative du/dt). An observation that u=0 has no information about whether du/dt=+v or -v if v is nonzero. This explains why a sign tag at an amplitude zero may be genuinely relevant to a WAVE FUTURE without claiming two spatial origin points.

Using exact rational source leapfrog recurrence

    u_(n+1)=2 u_n-u_(n-1)-(1/3) L9 u_n,

take u0=0 and u1=+delta_centre or -delta_centre. These have identical spatial amplitude zero, opposite wave velocity and different source futures. Both preserve the exact leapfrog energy 1/2. Remove the genuine Fourier DC component from the velocity (delta_centre - DC/9) and the two sign-dependent futures STILL differ. This is a true finite wave-phase-space non-FactorsThrough witness, not a physical SU(N) YM time generator. To interpret the double-centre sign as tangent polarity rather than provenance/gauge, require a source map orientation→nonzero tangent, and handle the v=0 case. Zero amplitude cannot have intrinsic nonzero amplitude sign.

The test is reproducible with the original full local SymPy checker under /mnt/data/ym_p0/check_ym_p0_centre_sign_wave_gap_20261123.py and a focused committed source-equivalent checker at ../scripts/check_ym_p0_centre_orientation_wave_os_boundary_20261123.py.

## Original Yang–Mills physical endpoint / max-cut

The original complete SU(N) Wilson 1024 native fine bonds, 1536 original plaquettes, 64 native R445 W=UV pair holonomies, 896 interacting spectators and original 1,F,G,FG closed marks MUST survive one source measure through F19 full constrained Haar and CMP119/122 native domain histories (Ω,Λ,S with S inside T, FP/Jacobian/gauge/R, E/R/B/V, β(a)). The exact previous four-mark BIDI and nonzero mixed connected determinant are finite conditional source tests, not a physical W3 absolute shell.

Next physical source cut: termwise ABSOLUTE original CMP116 marked Wilson connected charge uniformly decaying in actual physical SI separation against entropy and cutoff/volume; original interacting continuum, OS positivity and noncollapsed Schwinger fields; literal SAME reconstructed self-adjoint OS Hamiltonian H and translation/stress generator on the dense core; positive gap certificate from actual source, no pollution. Existing gap/same-H theorem compilers should be CONSUMED, not rebuilt. The added nine-sheet κ is forbidden as a proxy for physical YM gap. Retained zero-label wave state must either be shown OS-null (gauge) or get energy from original source, not by fiat.

The genuine 9-sheet centre, dual DC mode, physical gauge longitudinal null and RH actual ζ-zero or observed notch remain distinct typed objects; Singer k is an INDEXED CHART, not Euclidean physical t. H05 remains 8 vertices/12 maps/SIX faces. The original source units, history, signed zero, residual and admissible consumer matter.

Attribution: Wilson/Haar, Osterwalder–Schrader, Bałaban CMP98/109/116/119/122, classical C3² Fourier/graph wave geometry, and existing DASHI SU(N), original YM/RH/TOE, Leech-wave, Base369 groupoid and semantic descent theorem owners.


## Further original positive finite-transfer-gap donor (master audit)

Two additional original masters sharpen the operator/provenance distinction:
- DASHI/Physics/Closure/YMSprint107HamiltonianSpectralGapBridge explicitly records a POSITIVE **FINITE transfer-matrix gap** and the formal relation H(a)=-a^(-1) log T(a), but marks physicalHamiltonianSpectralGapProvedHereStatus=false, continuumNormalizationEvidenceCompleteHere=false and transferToHamiltonianTheoremLocallyProved=false.
- DASHI/Physics/YangMills/BalabanClayTransferHamiltonianGapSeparationExact explicitly carries different typed TransferGap and HamiltonianGap quantities with a conversion mapping dependent on the physical scale, and a conditional input for uniform physical conversion.

Thus it would be wrong to say that the repo lacks a positive Hamiltonian or spectral-gap framework; these donors ARE important existing owners. It is equally wrong to infer a fixed 4D continuum physical mass from a positive dimensionless transfer gap, a finite chosen Hκ stiffness, or a proof record containing its positivity as a required field. The source must pay the cutoff-independent lower bound for -log eigenvalue ratios divided by the actual physical lattice spacing, and prove the SAME reconstructed interacting OS H/observable sector. Retain original physical t and k separate.


## Exact scaling negative control: positive finite transfer gap can have zero continuum mass

The committed original-source wave checker now includes local **SymPy analytic limits** to reconcile master YMSprint107 and BalabanClayTransferHamiltonianGapSeparationExact. Write physical spacing a=1/n and a selected normalized transfer eigenvalue λ₂(a) in (0,1), so finite transfer gap δ(a)=1-λ₂(a)>0 and the corresponding candidate physical energy is E(a)=-log λ₂(a)/a.

Two positive-for-every-finite-n examples have opposite continuum outcomes:

    λ₂(a)=1-a²   =>  E(a)=-log(1-a²)/a -> 0;
    λ₂(a)=1-a    =>  E(a)=-log(1-a)/a  -> 1.

Both have strictly positive finite transfer gaps at n≥2; the first has ZERO physical continuum energy. Local SymPy 1.14 exact limits and positive n=2 tests PASS. This is not claiming that either chosen transfer spectrum is the original Wilson one: the counterexample proves that *finite spectral positivity alone* does not logically pay the uniform original Wilson/OS same-H mass-gap rate. Stronger proof obligation: a physically sourced, all-cutoff selected transfer eigenvalue ratio with -log(λ₂(a))≥m a for fixed m>0, plus source-proven T=e^(-a H_OS) on the identical interacting reconstructed Hilbert space and suitable spectral/core convergence; no cheating by choosing a different Hamiltonian for each chart.

The exact committed checker Git blob 1a61b644cc7f617acd69ee0a52ead50ec092337f matches the **locally executed** Python file byte-for-byte, including this counterexample. No CI or native Agda/Lean acceptance.
