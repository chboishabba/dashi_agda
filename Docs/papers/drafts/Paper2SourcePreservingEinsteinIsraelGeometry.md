# Paper 2 — Source-Preserving Dimensional Reduction and Einstein–Israel Geometry

**Subtitle:** Signed Hopf connections, periodic Kaluza–Klein fibres and AdS gravitational spectra  
**Status:** Revived independent working manuscript, 28 November 2026. Not a submission, native kernel certificate, or terminal GR/QFT/TOE claim.  
**Suggested classifications:** gr-qc; math.DG, math-ph.  
**Source:** [Hopf #1554, P0AK–AO and predecessors](https://github.com/chboishabba/dashi_agda/blob/7914ec131be930eb8baa237f3489930ec91c2d24/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md). Historical [Paper 2](../legacy/Paper2GRGeometryDraft.md) remains unchanged; its finite DCHoTT/Gate 4 construction is an independent antecedent, not assumed equivalent to the continuum metrics below.


## Current proof state — 28 November 2026 (BR177; reference reflection/paired trace BR175–176, full curved Cartan estimate open)

The periodic positive-tension Einstein–Israel development is a stronger selected branch, not the first or only classical gravitational realization of the Hopf geometry. P0T/U/V already give the noncompact vacuum KK and ideal Einstein–RMHD analytical local-development arguments under their stated assumptions; P0V derives the actual cylinder-invariant reduced Einstein–Maxwell–radion equations and distinguishes vacuum KK helicity acceleration from ideal RMHD helicity transport. Those results may be advanced and reported independently. Neither is a proof of the periodic AdS wall theorem. Existing source-specific TOE adapters consume actual FLM coordinate inverses and spectral reopening at shared-carrier grade, not universal dynamical or quantum equivalence.

BR124–139 supply the curved Gauss/electric Weyl mean-shape inverse, conditional same-metric projected Weyl uniqueness, positive compact-chart material energy, corrected reference subsidiary work and nonzero mean work cancellation, local compatible current and the torsion-aware trace budget. BR140–142 show, under matched intrinsic coframe/connection and full vacuum target jumps, that the tangential Cartan defect is common across the wall and the mixed jump retains intrinsic torsion. In the restricted spatial algebraic curvature sector the remaining mean work is the axial commutator of spatial shape and double-dual curvature; it need not vanish. Surface time transport of the defect retains the actual electric Bianchi trace. The bulk-to-wall trace, full variable coupled estimate, original higher corners, global exterior/holonomy and nonlinear generation remain open. The exact checker has three local PASS stages; no kernel or nonlinear acceptance. See the [controlling programme scope and proof register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).

### Historical BR89–91 proof-state snapshot

The latest original full warped reference uses BR37 rest-frame rank-one replacement in the positive adapted Hermitian endpoint norm, with E-sector factor max(1,|ξ|/|s|). This is a frequency-dependent norm conditional on the BR35/37 rest inverse and nonzero response, not uniform physical Sobolev coercivity. BR90 retains the full Einstein defect D=Ric+4g across the physical Israel jump: [D_na]=0 and [D_nn]=tr_h[D_ab]+6j tr_h M. The exact defect-to-Weyl rank is 9, projected zero-speed rank 6 and normal-symbol rank 8. BR91 retains all 75 first jets with five contracted Bianchi constraints; the compatible Cotton map has rank 25 and projected zero-speed rank 9 even on wave-compatible gauge Hessians. Contracted Bianchi alone therefore cannot remove this source. The proper route is reduced metric W1–W3, homogeneous gauge-wave IBVP on that same metric, then D=0 and vanishing Cotton/jump source; independent Weyl evolution needs its own geometric curvature comparison. These ranks were independently checked by a local SymPy transcription reported in the owner roadmap; the committed BR89–91 checker and full warped interval acceptance remain pending. BN spatial initial-data existence under its stated assumptions is not physical-time evolution. See [BR89–91 source cut](https://github.com/chboishabba/dashi_agda/commit/9d7044b487b3902860d515c74b0fb5b84ecc81e1).

## Abstract

We study source-preserving reductions of noncompact Hopf geometry with a compact fifth direction and distributional gravitational sources. A selected periodic AdS5 pure-tension background admits a direct Hopf deformation preserving the spatial Israel jump. A positive ground-state transform of its linearized Hamiltonian constraint yields a coercive inverse and nonlinear small-data comparison barriers; a finite-box weak discretization retains the full metric and surface source. An AdS3 slicing of the same undeformed metric gives a separated normalizable spin-two tower with a strictly positive lowest mass, distinguishing a geometric slice from an autonomous three-dimensional Einstein theory. Comparisons with the rank-24 Monstrous M-theory and Leech/FLM carriers give exact action and curvature discriminators, not a quantum duality. We separate classical background identities, candidate analytical proofs, executed finite controls, native certification and physical realization.

## 1. Geometry and authority

Use units with speed of light one, \(\kappa=\kappa_5^2\), a periodic proper coordinate \(y\in[0,L]\) with endpoints identified, and a common oriented unit normal across the single brane. The bulk obeys \(G_{AB}+\Lambda_5g_{AB}=\kappa T_{AB}\). Brackets mean plus minus minus, not two independently outward normals. Israel's equation is
\[
[K^a{}_b]=-\kappa(S^a{}_b-\tfrac13\operatorname{tr}S\,\delta^a{}_b).
\]
In the original noncompact Ricci-flat G3 construction the rational Hopf potential on Euclidean three-space is
\[
 A_0=\frac{2(2xz-2y_0,2x+2y_0z,1-x^2-y_0^2+z^2)}{(1+x^2+y_0^2+z^2)^2}\cdot d(x,y_0,z).
\]
Here \(y_0\) is a base coordinate, not the circle coordinate. Its oriented helicity integral is \(4\pi^2\). The Ricci-flat G3 branch, sourced periodic AdS comparison, original electromagnetic/RMHD G4 branch and actual DCHoTT finite carrier are distinct; they require independent realization maps. No ordinary electromagnetic field is inferred solely from the metric connection.

For a spatial conformal factor with time symmetry, fixed physical surface density and smooth seed, the scalar constraint in four spatial dimensions includes the surface delta with its conformal scaling. A uniformly positive extended tension is incompatible with the earlier asymptotically product, Lambda=0, time-symmetric conformal seed: averaging over the circle and then spheres gives a positive uniform forcing of the Newton equation and contradicts convergence to one. This is a restricted obstruction, not a general prohibition of extended tension.

## 2. Exact periodic source background

Take \(\Lambda_5=-6c^2\), \(c>0\), and a four-dimensional AdS metric of sectional curvature \(-h_0^2\). Set
\[
 g_5=dy^2+b(y)^2g_{\mathrm{AdS}_4},\quad
 b=\frac{\cosh(c(y-L/2))}{\cosh(cL/2)},\quad
 h_0=\frac{c}{\cosh(cL/2)}.
\]
Then \(b''=c^2b\), \((b')^2=c^2b^2-h_0^2\). The warped Ricci formula gives \(R^A{}_B=-4c^2\delta^A{}_B\) on the smooth bulk. At the seam \(b=1\), \([b'/b]=-2c\tanh(cL/2)\), so the full pure-tension Israel equation holds for \(\kappa T=6c\tanh(cL/2)\). The minimum at \(L/2\) is smooth, not a second brane.

For a general static warped maximally symmetric slice of curvature C and tangential bulk Lorentz-invariant stress with density \(\rho_b\) and transverse pressure \(p_y\), the integrated Einstein difference reads
\[
 \sum_iT_i+\int_0^L(\rho_b+p_y)dy=-\frac{3C}{\kappa}\int_0^L e^{-2A}dy .
\]
Flat slices with one positive tension require the integral on the left from bulk matter alone to be \(-T\). The flat-circle Casimir potential cannot be substituted without its actual warped/brane-dependent stress tensor. These are classical warped-product and junction identities, not claims of new general relativity theorems.

## 3. Hopf deformation preserving the seam

Use the time-symmetric hyperbolic spatial base \((\mathbb H^3,\gamma)\) of curvature \(-h_0^2\). Pull back the original Hopf one-form through the oriented radial diffeomorphism \(r_{\mathbb R^3}=\sinh(2h_0r_H)/(2h_0)\). Let \(a=\epsilon A_0\), \(S=1+|a|_\gamma^2\), and \(H=\gamma+a\otimes a\). Choose the explicit periodic spatial seed
\[
 g_\epsilon=(dy+a)^2+Q,\qquad Q=\gamma+(b^2-1)H/\sqrt S.
\]
The eigenvalues of Q relative to gamma are \(1+(b^2-1)/\sqrt S\) on the transverse plane and \(1+(b^2-1)\sqrt S\) in the a direction. Thus for uniformly small epsilon the metric is positive; it is continuous and piecewise smooth at the seam. At epsilon zero it is exactly the background spatial slice. At the seam its induced metric is H, \(g^{yy}=S\), and the common unit conormal is \(dy/\sqrt S\). The tangential derivative jump satisfies \([\partial_y g_{ij}]=2[b']H_{ij}/\sqrt S\). Hence
\[
 [K^i{}_j]=\frac{\sqrt S}{2}H^{ik}[\partial_y g_{kj}]= -\kappa T\delta^i{}_j/3.
\]
For fixed tension the instantaneous lapse seed \(N_0=N_{\rm base}b^{1/\sqrt S}\), with continuous tangential base lapse, supplies the temporal jump after the conformal correction below. A general rest stress \(S^a{}_b=\operatorname{diag}(-\rho,pI+\pi)\) with trace-free pi requires \([K^i{}_j]_{TF}=-\kappa\pi^i{}_j\) and \([K^t{}_t]=\kappa(2\rho/3+p)\). The isotropic construction does not pay that extra anisotropic source or material evolution. Vanishing initial extrinsic curvature of the time slice and vanishing material momentum satisfy the initial momentum equation; they do not determine future evolution.

## 4. Hamiltonian constraint and small-data comparison

Let physical spatial metric be \(u^2g_\epsilon\) and let the selected tension remain fixed. Smooth and distributional equations become
\[
 -\Delta_\epsilon u +\tfrac16R_{\epsilon,reg}u-\tfrac13\Lambda_5u^3=0,
 \qquad -[\partial_\nu u]+\tfrac{\kappa T}{3}(u-u^2)=0.
\]
At zero deformation, the linearization at u=1 is \(\mathcal L=-\Delta_{\bar g}+4c^2-(\kappa T/3)\delta_\Sigma\). The warp itself obeys \(\mathcal Lb=3h_0^2/b\); its normal derivative jump cancels the delta term. For compactly supported smooth test functions (and by form closure),
\[
 q[v]=\int b^2|\nabla(v/b)|^2dV+\int (3h_0^2/b^2)|v|^2dV\ge3h_0^2\|v\|_2^2.
\]
This is a scalar initial-constraint coercivity estimate, not a tensor/radion dynamical stability theorem.

For the selected radial map, use \(\eta=\mathrm{sech}^2(h_0r_H)\), \(\Delta_{\mathbb H^3}\eta=-6h_0^2\eta^2\), and \(w=(1+(b-1)/\sqrt S)\eta\). Lower and upper barriers \(1-\delta w\), \(1+\delta w-2\delta^2\eta^2\) have exact boundary residuals \(-\kappa T\delta^2\eta^2/3\) and \(\kappa T\delta^2\eta^2(1+4\delta\eta-4\delta^2\eta^2)/3\). At epsilon zero the first variation in direction w is bounded below by a positive multiple of eta. Under the uniform piecewise C2 weighted estimates, smallness, trace and compactness hypotheses recorded in AM, the same strict bulk signs persist for sufficiently small epsilon relative to delta. Shifted monotone iteration on exhausting bounded domains gives a candidate positive weak solution with \(|u-1|\lesssim\delta\eta\). The analytical proof needs independent review of these hypotheses and the exhaustion passage; no explicit certified radius is supplied. The conformal jump equation gives the physical mixed spatial jump exactly when a sufficiently regular solution exists; the lapse \(uN_0\) gives the same initial temporal jump in the adapted rest chart. No full timelike development is inferred.

## 5. AdS3 slicing and tensor spectrum

Rewrite the exact undeformed background with \(f(z)=\cosh(h_0z)\):
\[
 ds_5^2=dy^2+b(y)^2(dz^2+f(z)^2ds_{\mathrm{AdS}_3}^2).
\]
The local AdS3 slice is part of the same object. The constant-profile Einstein–Hilbert coefficient is proportional to \(\int b^2dy\int_{\mathbb R}f dz\), which diverges. For the standard external TT relative metric amplitude, normalizable self-adjoint boundary and periodic pure-tension matching, use norm \(\int b^2 f |q|^2\) and energy \(\int (b^4f^3|q_y|^2+b^2f^3|q_z|^2)\). Separate the compact operator \(-b^{-2}\partial_y(b^4\partial_y)\) with eigenvalues \(\mu_j^2\ge0\), including constant zero mode. Put \(a_j=(3+\sqrt{9+4\mu_j^2/h_0^2})/2\). The normalizable separated solutions are proportional to
\[
 Z_{jn}=\operatorname{sech}^{a_j}(h_0z)C_n^{(a_j-1)}(\tanh(h_0z)),\quad
 m_{jn}^2=h_0^2(a_j+n)(a_j+n-2).
\]
Conjugation to the Gegenbauer differential operator and polynomial density in its weighted L2 space yield the candidate all-index spectral proof under the stated self-adjoint domain. For j=0, ground state \(\operatorname{sech}^3\) has norm squared \(3\pi/(8h_0)\) in z, and ground-state energy gives \(m^2\ell_3^2\ge3\) with equality. The spin-two dimension on the standard normalizable branch begins at 3 rather than 2. Neither this result nor the divergent zero-profile integral rules out all boundary gravity constructions. It specifically rules out autonomous massless EH gravity in this selected normalizable tensor sector; no nonzero-Hopf spectral or quantum equivalence follows.

## 6. Moonshine comparison and residual preservation

At the same bulk Lambda an alternative Einstein product AdS3 x compact hyperbolic surface of genus g>=2 has sectional curvatures \(-2c^2,-4c^2\), finite reduced G3, and Brown–Henneaux c=24 when \(G_5c^3=\pi(g-1)/(16\sqrt2)\). It is NOT the original periodic Hopf background: Weyl-squared differs by \(72c^4\) from local AdS5, and product-brane Israel stress is anisotropic. Equal Ricci tensors and central-charge parameters are insufficient. Parity-even EH also gives two chiral central charges, not a single holomorphic Monster theory.

The separate Paper 10 source supplement handles the exact M2 exterior polarization reduction, Leech quotient and binary/ternary representation transport; it is a comparison, not a premise of the gravitational constraint. The existing Paper 8 closure grammar can consume the positive quadratic form, normalizable weighted Hilbert carrier and explicit non-descent examples. A Ricci contraction forgets Weyl; a horizontal KK observation forgets the compact connection; a character forgets actual representation operators. Their residuals are source-specific, not one identified physical field.

## 7. Executed checks and reproducibility

Prior committed source receipt: #1554 head 7914ec131be930eb8baa237f3489930ec91c2d24. The reported local runs are not fresh executions for this manuscript. See [P0AK–AO roadmap](https://github.com/chboishabba/dashi_agda/blob/7914ec131be930eb8baa237f3489930ec91c2d24/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md) for exact predecessor hashes, commands, source assumptions and negative controls.

- scripts/check_hopf369_p0ak.py: 25 Ricci components, seam identities, scalar coercivity identity and four 1D FEM controls.
- scripts/check_hopf369_p0al.py and p0am.py: AdS3 slice, curvature discriminator, Hopf seed and boundary barriers.
- scripts/check_hopf369_p0an.py: all-index Gegenbauer conjugation and 27 finite polynomial controls.
- scripts/check_hopf369_p0an_metric.py (as extended at P0AO): actual 4D full metric AD curvature, periodic Q1 volume and nonlinear seam solve, finite Poincare-ball cube with artificial Dirichlet boundary. Six positive-amplitude refinement comparisons at c=1, L=2log2, h0=.8, kT=3.6, epsilon=.025 converged in two Newton steps with maximum discrete weak residual about 2.24e-15. Raw area-weighted seam derivative residual decreased from 1.31e-4 to 3.08e-5; the final relative RMS is about 29%. This is not a certified strong junction trace, full ball exhaustion, continuum rate or error interval. Original signed circle-reflection control at two meshes passed to 2.22e-16.

## 8. Remaining exact endpoints and submission prerequisites

1. Independent review of the explicit seed, normal convention, scalar coercivity, barrier weighted regularity/exhaustion and TT boundary/Israel derivation; literature search to distinguish classical results from source-specific candidate novelty.
2. Full hyperbolic exhaustion and equilibrated normal flux, trace estimates, rigorous a posteriori norm bound and mesh/normal convergence; no inference of strong trace from Newton residual.
3. Same-source Lorentzian Einstein–Israel evolution with appropriate gauge, initial/boundary corner compatibility and actual AdS boundary conditions. Import F8 operators only after matching metric, action, tensor domain and source; preserve constraints and energy.
4. Actual anisotropic source, conserved mechanical and gauge/chemical stress, renormalized warped Casimir source if used, and independent physical calibration.
5. Separate native proof interfaces and exact-head Agda/Lean acceptance if claiming formal certification. No new kernel result or full dependency replay is claimed.
6. Neither this continuum comparison nor the historical Paper 2 finite geometry constructs the actual DCHoTT-to-continuum isomorphism, W4 physical matter source, universal action, or quantum Monster duality. Keep promotion flags false.

## References and attribution

Israel (1966), DOI 10.1007/BF02710419; standard KK and Einstein warped-product geometry, Hopf helicity, conformal initial-value and Gegenbauer/Sturm–Liouville theory; Brown–Henneaux (1986), DOI 10.1007/BF01211590; Witten arXiv:0706.3359 (conjectural quantum gravity); Chester–Marrani–Rios, Monstrous M-Theory, DOI 10.3390/sym15020490; FLM, *Vertex Operator Algebras and the Monster* (1988). Existing KSW668/F8, KK radion, source and signed-geometry owners retain their recorded attribution. DASHI contribution is the particular source-compatible Hopf seed, constraint/spectral integration, exact discriminators and executable checks; novelty against literature is not yet certified. Credit JMD only for evidenced upstream geometry/diagrams or explicit donor material, not for classical GR or the Leech construction. Preserve earlier original Hopf/ABHA source genealogy in #1554.


## 26 November 2026 — off-shell action and complete brane metric variation (AP)

The [AP original source ledger](https://github.com/chboishabba/dashi_agda/blob/fcff38380da21f163876f6204758e2db38a18559/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md) adds an action check independent of the curvature substitution. With normal lapse N(y), continuous periodic warp b(y), fixed tension and distributional EH (or equivalent cut-interval boundary terms, not both), the reduced density per sqrt(-g4)/(2k) is N b² R4+12 b² b'²/N-2 Lambda N b⁴, with surface -2kT b(0)^4. Lapse and warp variation reproduce the actual smooth background equations; periodic seam variation yields [b']=-kT b/3. For I2=int b²dy, I4=int b⁴dy at the actual AK solution, 4c² I4-3h0² I2=kT/3. Thus at fixed warp, the entire admissible base metric action family equals the EH family with k4=k/I2 and Lambda4=-3h0², subject to matched external boundary terms. This is not a full KK consistent truncation or a reduction of arbitrary nonzero Hopf perturbations.

For a fixed timelike graph X=(x,f(x)), local KK chart G=g+r(dy+A)^2, a=A+df, H=g+r a a^T, Delta=1+r a^T g^-1 a>0, the actual tension action equals -T int sqrt(-det g)sqrt(Delta). Every symmetric ambient tangent D corresponds bijectively to (dg,dA,dr) at r>0: dr=D55, dA=(D_mu5-A dr)/r, dg=D_muν-dr A A^T-r(dA A^T+A dA^T). Induced tangent equals P^T D P, P=dX. The exact variation is -T/2 int sqrt(-det H) tr(H^-1 P^T D P); projected source variations in g, A and r jointly recover all ambient directions. A fixed embedding variation does not establish its normal shape equation or a separate Maxwell field. For y-dependent metrics retain actual evaluation and gauge diffeomorphism. The scalar constraint energy from Section 4 has a different variational functional, not the Lorentzian physical Hamiltonian.

New [checker](https://github.com/chboishabba/dashi_agda/blob/fcff38380da21f163876f6204758e2db38a18559/scripts/check_hopf369_p0ap.py) locally passed four groups, including 30 exact rational selected variation directions and full inverse ambient tangent chart for 15 directions. Native Agda/Lean path and coefficient source terms are not kernel certified. No new continuum solve. This pays a selected classical action/metric variation case, not the TOE universal action, literal selected QFT, full Hopf Einstein evolution or calibration.

## AQ — signature and causal geometry from the original TSFV/KK owners

[Source audit and exact controls](https://github.com/chboishabba/dashi_agda/blob/06c9ea82a186c9156f2f92c41d4fe653de3278c8/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md). Use the original TSFV selected observer and same metric records, not a newly chosen signature label. With g nondegenerate and positive fibre matrix R, the original shear generalizes to G=B^T diag(g,R) B, B=[[I,0],[A,I]]: the inertia is additive. A (3,1) base gives (4,1) for one and (5,1) for two positive fibres; the original AK source uses one. A (4,0) base gives (5,0) with one fibre. Original DASHIfine positive-five diagnostics are distinct fitted operators, not a real continuation to Lorentzian signature; no recovered original six-axis empirical result. The tangent causal cone projects exactly to the base causal cone with horizontal lift; a timelike base direction q<0 gives two signed null endpoints -A(v)±sqrt(-q/r). The dual symbol retains (p-A^T k)^T g^-1(p-A^T k)+k^T R^-1 k, and k=0 recovers the base symbol. Nonzero signed modes require the actual coefficients and domain; y-dependent geometry does not imply exact Fourier decoupling.

Finite marked null probes in a chosen orthonormal frame (e0±ei and e0+3ei/5+4ej/5) fix the symmetric form up to positive scale: opposite probes force time-space terms zero and spatial diagonals equal minus the temporal diagonal, mixed probes force spatial cross terms zero. Exact ranks 9,14,20 for 4,5,6 dimensions. A calibrated timelike norm fixes the remaining scale. Diagonal signs alone do not imply inertia and two-time selected half-cones need not be convex. Actual TSFV finite access order is not this spacetime cone until selected physical observer state, signal response, frame, scale and metric are identified. Existing same-arrow and full KK tomography proof owners reused. Local exact checker PASS; native source uncompiled. No independent observed dimension, OS reconstruction or full Einstein evolution claimed.

## AR — selected TSFV retarded continuum comparator

The [original TSFV source owner](https://github.com/chboishabba/dashi_agda/blob/9d9858acf47fada4e9f16dc6e25de3c5117683fc/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md) supplies a quantitative extension of the chosen cubic scalar-lattice comparator, not another physical metric assumption. With κ=c²/a², L_a=mu² I+κ(6I-adjacency), the local velocity impulse has first nonzero odd derivative at graph distance d at order 2d+1, with value κ^d times shortest path count. Marked neighbour and centre third derivatives jointly identify κ and mu². At fixed torus side length, the continuum lambda=mu²+c²|p|² and discrete lambda_a satisfy 0<=lambda-lambda_a<=c²a² sum p_i^4/12. Duhamel and |sin(t sqrt(lambda))/sqrt(lambda)|<=t give |K_a-K|<=c²a²t³ sum p_i^4/72, including the massless zero branch. Smooth-test Fourier sums yield distributional convergence on compact time intervals; no exact finite-grid spatial causal support. The physical clock and spacing identify the selected acoustic principal metric, and the local proper causal-diamond volume is pi(cT)^4/24 in the chosen 3+1 continuum. Neither the chosen graph nor its calibrated metric is the original TSFV physical observer; the latter's finite ABL instance has singleton time and identity evolution. The standard selected oscillator unconditioned Kubo kernel equals this classical kernel; postselected response is not inferred. Local source-linked tests: 575 exact graph coefficients, 15500 sampled response bounds, observed second order. Native source terms uncompiled. Do not substitute this flat comparison for the nonflat periodic Einstein-Israel background or claim original TSFV physical realization.


## AS — original ABL source clock and emitted-record field dynamics (26 Nov 2026)

[Original TSFV #1460 AS source](https://github.com/chboishabba/dashi_agda/blob/63d516957ce2ddeb607ea47f4f92a33181a94ef0/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md) supplies a selected actual-complex-carrier three-tick unitary swap clock with transported endpoint preparations: original forward/backward states, all transition amplitudes, ABL denominator and outcome probabilities reopen at middle. Existing QuantumSurface, original projectors and pairing reused; native source uncompiled. Independent selected spatial extension uses original certified controlled environmental rotations on local |0>,|1> oscillator record subspaces at distinct marked sites of the original 125-site lattice. Both branches propagate under the same quadratic coupled Hamiltonian, preserving original overlap under transported final environmental selection. Explicit ABL success weighting recovers the unconditioned marginal under complete final measurement. Exact central field commutator equals AR retarded kernel in this selected model; weak normalized commutator needs nonzero coherent overlap, not merely positive ABL denominator. Late pointer rotation can alter conditional probabilities without changing earlier unconditioned records. Local exact checker PASS: 27 clock compositions, 40 pulse lists/120 complex gamma controls, 32 full 125-site polynomial-domain commutator controls. Verified blob 9c9c1568d4b9acf44cc082adf39f54e763675f43; Lean #122 6a47da0 source companion. Actual calibrated physical clock, original observer instrument, independent spatial/dimension measurements, selected Hopf metric identity, interacting OS/action and continuum instrument limit remain. No native compilation, CI, experiment, physical promotion or new universal framework.


## AT — coordination geometry and conditional field response (26 Nov 2026)

[Original TSFV #1460 AT source](https://github.com/chboishabba/dashi_agda/blob/d4bfbc0f85cf52a73baaf0a1573e5a98c245347e/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md) connects the user's centered-square/Delannoy recognition of the AR diagram to the original impulse producer. Classical fixed-dimension ball D(m,R)=sum_k 2^k C(m,k) C(R,k), shell GF ((1+z)/(1-z))^m; original clipped counts 1,4,8,10,8, odd response derivative labels 2r+1 distinct from amplitudes and causal times. Actual 5³ torus shell polynomial (1+2z+2z²)^3 has counts 1,6,18,32,36,24,8, whereas shortest-path exponential polynomial (1+2z+z²)^3=(1+z)^6 yields d! C(6,d) response multiplicities. Retain signed displacements, zero and path residual, no finite-a light cone or independent dimension emergence. Original bounded field effect and kick on actual AS emitted-record oscillator give exact normalized derivative P'_r=(w'_r D-w_r D')/D² and inverse w'_r=D P'_r+P_r D'; binary selection covariance retains signed likelihood residual. Full final measurement restores unconditioned earlier records. Local checker c154527f9dd022dc9bfb14532827dc7f8fe9a51c passes 25 exact Delannoy counts,125 torus path counts,16 floating field controls (max derivative error 5.03e-12),125 free massive mode OS Gram and transfer controls. Native existing Agda owners extended, Lean #122 3769dac source terms uncompiled. Master OS original energy graphs, shifted resolvent and strong functional-limit owners reopened; #1492 is original source branch, not reimplemented. Positive Euclidean transfer determines selected mode energy by log, real-time phase aliases; AS reference record vacuum distinct from coupled ground-state OS covariance. Original interacting physical observer, calibrated source clock and metric, actual OS reconstruction/real-time domain, noncompact continuum and universal action remain unpaid. No CI, kernel or promotion.


## AU — weighted impulse inverse and noncompact selected free source (26 Nov 2026)

[Original TSFV #1460 AU source](https://github.com/chboishabba/dashi_agda/blob/b2889f74222e997d08e6944705ae785d0ccb3e93/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md): all marked third-derivative columns J=-L reconstruct symmetric edge weights W_xy=J_xy (x!=y) and local mass m_y=-sum_x J_xy; shortest response sums weighted shortest paths, signed cancellation counterexample even with positive stiffness. Calibrated six-direction principal matrix recovers selected stencil coefficients; opposite diagonal vs doubled axial stencils same D but quartic residual 12 p_x² p_y². Retain actual signed source, zero, cutoff and dispersion residual. Original constant-stencil retarded Fourier embedding extends AR to R³: uniform compact-time Schwartz-test bound a²T³/72 integral weighted fourth moment plus T omitted Brillouin-zone tail; simultaneous L→infinity and a→0 by compact Riemann sums and uniform Schwartz tails, strong L² retarded convergence for initial velocity, not point delta. Selected fixed positive D coordinate action equals covariant scalar action at phi=(det D)^(1/4)q, not full metric-variation or universal-action identity. Massive Gaussian reflection-positive kernel and dGamma(sqrt(lambda)) give same selected free H for positive Euclidean transfer and real unitary group, with vacuum energy normalization and zero mode distinction. Actual #1492 energy-graph/Hilbert owners reopened; finite original C² pointer is not surjectively equivalent to full Fock, original physical extension/clock and interacting OS authority still needed. Smeared instrument convergence conditional on matched states, symplectic forms and success bounded away from zero; no point-instrument or site-record UV limit asserted. Local executed checker d85ed13c6d3cef53141e75459cd673df8361f965: 15625 exact entries,125 mass residuals,575 weighted path controls; selected Gaussian quadrature error 3.846e-6→6.022e-8, orders approaching2. Native original Agda anisotropic coefficient source, Lean #122 1193dd7 uncompiled. No CI, physical experiment, universal action, Hopf identity, or paid flags.


## AV — original-owner reconciliation and finite-energy source cut (26 Nov 2026)

[AV original TSFV roadmap](https://github.com/chboishabba/dashi_agda/blob/3dd7d3e345d55428f23a82c5e55f298d94e99c27/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md): actual master cyclic positive functional, action quotient, Bishop complex sesquilinear span transport, R445 all-word/finite-span and OS energy-graph/functional-limit owners inspected. Do not rebuild them. Primitive source M1 cylinder readout, M2a scoped multiplicative cylinder, M2b selected physical reflection adjoint; existing full-algebra commutativity no-go prohibits onto noncommuting algebra. Full complex Gram can be recovered by four matched squared norms on same complex span; real R445 readout insufficient. Selected full 2x2 forward functional omega(A)=psi†Apsi/2 on original psi=(1,1), nonfaithful null ideal and cyclic quotient C², not full field Hilbert. Selected normal-mode site packet UV lower bound E>=4 c_x/(pi a); AS product-vacuum distinction retained. Fixed smooth orthonormal modes via projected Gram inverse square root preserve original pulse overlap, finite Fock energy including off-diagonal coherence, and bounded smeared instrument limit with positive success. Four-dimensional densitized inverse H=diag(-rho,K), v=sqrt(-det H), g^-1=H/v, sqrt(-g)=v, mass²=V/v recovers full coordinate action without metric-dependent field rescaling; cone D=K/rho alone insufficient. Selected laminate harmonic normal/arithmetic tangential cell formula; general homogenization unpaid. Actual local checker final blob d5dec7b85857b0048dbb92648fa52af7be9cd037, commit da64940db00d3964100e0f12f4fe5d90e110d5ab: exact symbolic controls, selected UV quadrature and full coherent smeared packet energy. Lean #122 eb73a9b source algebra uncompiled. Remaining source cut A–K in original roadmap, includes actual physical state, instrument, clock, complex Gram/density, actual OS, metric/curvature, same source nonzero Hopf constraints and junction, QFT action/stress, independent FLM/M²/H05/H07. F8 nonlinear source already exists but actual constraint/Israel evolution remains, no promotion. No CI, kernel or physical measurements.


## AW — consolidated execution and actual implementation (26 Nov 2026)

[Canonical AW execution contract and receipt](https://github.com/chboishabba/dashi_agda/blob/94cc953a6e128b523a02402c0a35c131f8ed3dc6/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md) maps every AV obligation to AW1–AW5: AW1 original complex observer/instrument (A/B/C/D1/H2), AW2 Hilbert/OS/domain (D2/E/F), AW3 geometry (G/H1/B4), AW4 actual Einstein–Israel (I/J2), AW5 actual QFT/action/stress (J). Parallel FLM/Monster, M², indexed hyperfabric and quantum boundary retained. No scope expansion to unrelated Clay work. Original finite ABL Positive requires numerator >=1, incompatible with nonnegative Hilbert norm at zero; original Hilbert-law interface must separate these predicates, not change ABL. Original finite matrix action/adjoint/cyclic section and normalized Gram now source-written in existing Agda owner aeeaac6. Selected spectral derivative domain both directions via dominated convergence/Fatou, resolvent/functional calculus only on actual matched isometry; no actual original OS identification. Full four-dimensional metric density tangent inverse (including mixed directions) and fixed-mass scalar action variation analytically derived, independent potential variation retains -q²(dV-m²dv)/2. Variable-mass scalar Ward identity retains external force -q² dM/2; full Hopf constraints/junction/evolution not claimed. Local executed checker 4a9a5fd6e97396e7e25465f025402019e3e50645 matched committed c4c03a3, all three groups PASS: exact complex algebra, 20 floating spectral bound controls, ten exact mixed metric tangent/stress directions and variable mass Ward. Lean #122 12c5f4c source terms. Native executables absent, no kernel or CI. Original source M1/M2, actual physical vacuum/clock and OS, general nonhomogeneous limit, full Einstein–Israel and literal selected QFT/universal action and empirical calibration remain. AW1–5 acceptance conditions explicitly maintained; no paid flag changes.


## AX — selective YM donor, normalized original Hilbert input and conservative scalar path (26 Nov 2026)

[Canonical AX receipt](https://github.com/chboishabba/dashi_agda/blob/3358a908d803893f1e32ba22c96c19ad56c266d1/Docs/roadmaps/TSFVUnificationExecutionPhasesDeliverablesExactLemmas20261106.md). Master YM terminal/L5/L6 and newer CMP/R445 sources inspected as donors only; candidate receipt flags do not supply actual original TSFV/OS or Clay proof. No YM work changed. Original Hilbert positivity now separates ordered scalar cone from ABL admissibility (32628a7,e3e69f7); actual normalized selected Matrix2C view of original pointer inhabits repaired source record with real nonnegative selfpair including zero and consumes original cyclic Gram/left kernel/section (c7d3529,a113729). Original ABL surface remains unchanged; normalization half scales amplitudes, cannot transfer stronger ABL admissibility automatically. Twelve globally nondegenerate elementary shear paths verify selected scalar coordinate/covariant action equality and stress variation, reuse underlying CMP119 derivative congruence, NOT YM/Maxwell-labeled record with scalar substitutes. Coupled canonical scalar potential (m q²+b z²+l q²z²)/2 supplies compensating signed variable-mass exchange and conserved total stress on both equations, not actual Hopf matter identification. Local exact SymPy checker 2b1c3b9 blob 1c2f530d273dd6cd1e166ca2cf52e14623bc83ed PASS all three groups. Native source uncompiled; no CI, physical experiment or promotion. Retain original M1/M2, actual complex/OS completion and calibration, general continuum, full nonlinear Hopf Einstein–Israel and actual QFT action/stress. Next original coupled Hopf constraint and strong junction source, no generic framework or Clay YM scope change.


## AY — actual strong spatial junction and second-normal-jet compatibility (26 Nov 2026)

[AY canonical Hopf roadmap](https://github.com/chboishabba/dashi_agda/blob/cdabe0574ef5b3f6ba615219c2e8be74eb2b9a8c/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md). Reopened actual AM/AO source and master F8 nonlinear curvature; use original geometry not F8 model substitution. Exact reciprocal w=1/u-1, f=1+(b-1)/sqrt(S), w=f z smooth periodic gives strong nonlinear spatial seam by construction; bulk F(u)(1+w)^3=(1+w)Delta w-2|grad w|²+(Rreg/6)(1+w)²+2. Original nonzero eps=.025 six finite-box spectral resolutions (sine B=.36/poly B=.48), 24/135/448 coefficients, wall <=1.031e-18, independent test RMS bulk at finest .00510747/.00206002, not a solved continuum constraint. Ground-state test phi=u² f has exact linearized seam; conditional coercivity and reciprocal barrier criterion derived, sampled min>=1.8718 not uniform certified. Fixed-wall zero-shift time-symmetric gauge: spatial k±=M±jH/2, lapse [nN]=jN, ell=mean(nN)/N, mean timelike trace tr M+ell=0. J2=[partial_n k_ab] covariant, [ddot H]=2N²(J2+j(tr M+ell)H), scalar curvature jump=-2tr J2; hence five trace-free components remain beyond scalar constraint. Actual full metric AD on 27 seam points gives first jump 8.873e-16, TF second jet max .1840874. Two-sided collar second-jet correction delta D±=∓J2^TF/2+(R±-2Lambda)H/6 pays both scalar seam values and J2 locally, actual sampled algebra residual <=7.238e-16. No re-integrated corrected metric or coupled bulk solution yet. Next AZ: construct actual smooth tensor collar, re-solve coupled scalar/second-jet constraint, validate full-ball bounds, lapse/mean trace, then full evolution with existing F8. Three local/fetched checker blobs 0083391a63d2abe9328208c2dc23c547c0fbc776,486312bc0490057352c99578875a4bc3a96c9d30,3dc8f9d3becca61ec8864ced729abad5b8421d92. No native kernel, CI, full continuum or physical promotion; TSFV/OS, literal QFT/stress and independent Monster obligations retained; no YM edits.


## AZ–BC — intrinsic evolution and two-sided analytic Einstein–Israel development (26 November 2026)

Source custody: [canonical BC roadmap](https://github.com/chboishabba/dashi_agda/blob/f3ea6694bad964b4a67a1a4de4aa6b891d7416ac/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md), [BB wall checker](https://github.com/chboishabba/dashi_agda/blob/c50a7986e2bcb79a616172864a5b999a39fb2432/scripts/check_hopf369_p0bb.py), [BC normal checker](https://github.com/chboishabba/dashi_agda/blob/c71d659a35aa18056f42423069984e6fbfe8d4c6/scripts/check_hopf369_p0bc.py). These are selected geometry results; the classical Einstein, Israel, Gauss–Codazzi, Bianchi, Cauchy–Kowalevski and symmetric-hyperbolic existence machinery is prior art, not claimed as new.

### Intrinsic local evolution

For a timelike four-dimensional wall with induced metric \(h=-dt^2+H\), let \(H=e^{2p}H_0\), and prescribe the trace-free spatial endomorphism \(Q\) from the original Hopf seed, self-adjoint with respect to \(H_0\). Write the trace-free mean extrinsic tensor as \(M_{tt}=\sigma,\ M_{ti}=B_i,\ M_{ij}=H_{ik}(Q^k{}_j+\sigma\delta^k_j/3)\). In a common oriented spacelike normal, \(K_\pm=M\pm jh/2\), where the constant jump is \(j=-\kappa T/3\). The intrinsic constraints for the selected vacuum \(\Lambda=-6\) are

\[
 R_h+12-3j^2+\operatorname{tr}((h^{-1}M)^2)=0,\qquad
 \nabla^a M_{ab}=0.
\]

With \(v=p_t,\ P_i=\partial_i p\), the principal blocks of the intrinsic system are \(v_t=(2/3)H^{ij}\partial_iP_j,\ (P_i)_t=\partial_i v,\ \sigma_t=H^{ij}\partial_i B_j,\ (B_i)_t=(1/3)\partial_i\sigma\). Lower-order terms and source data are specified in BA/BB. The positive symmetrizer is \(v^2+(2/3)|P|_H^2+\sigma^2+3|B|_H^2\), augmented by \(p^2\). The derivative compatibility condition propagates; the characteristic speeds in an orthonormal wall frame are \(0,\pm\sqrt{2/3},\pm1/\sqrt3\). Standard local symmetric-hyperbolic existence/uniqueness therefore applies to smooth compatible data on compact local domains with positive \(H\). This does not make the spacelike-normal Einstein problem a smooth well-posed Cauchy problem. The ansatz selects a class of brane geometries, not a universal brane dynamics law.

BB actually evolves the original nonzero Hopf wall on a \(31^3\) seed lattice, rather than a replacement metric. Independent temporal differences reduce Gauss/Codazzi residuals from \(6.246\,10^{-5},9.959\,10^{-5}\) to \(1.561\,10^{-5},2.489\,10^{-5}\) when the time step is halved. An independently translated chart on the same lattice spacing agrees on 125 interior overlap points to \(6.939\,10^{-18}\) in maximum state component. These are time-refinement and finite overlap checks, not spatial convergence or an analytic global atlas.

### Local analytic normal development and retained third jet

Let \(g_5=dn^2+h(n,x)\), \(K=h_n/2\), \(\tau=\operatorname{tr}(h^{-1}K)\), \(E=\operatorname{Ric}(g_5)+4g_5\). The tangential equations give

\[
 D=K_n=\operatorname{Ric}(h)+4h-\tau K+2Kh^{-1}K,\qquad F=D_n.
\]

The signed cubic normal metric is \(h(n)=h_0+2nK+n^2D+n^3F/3\). On the wall \([D]=0\) follows from the trace-free mean and pure-tension jump. However, with \(u=\tau_n\) (common to both sides), differentiating the normal equation gives

\[
 [F]=j(8-u-j^2)h-12jMh^{-1}M.
\]

Indeed, constant scaling invariance of intrinsic Ricci gives \([d\operatorname{Ric}_h(2K)]=0\), and the terms linear in \(D\) cancel. Writing \(q=\operatorname{tr}((h^{-1}M)^2)\), the normal scalar constraint gives \(u=4-j^2-q\); hence \([F]=j(4+q)h-12jMh^{-1}M\). Equality of third-normal jets is not generally required by Israel matching. A local symbolic matrix check verifies all 16 entries of the unspecialized jump formula. This is a derived identity within the selected source geometry, not a new junction law.

For exact analytic nondegenerate wall data satisfying the intrinsic constraints, the tangential normal equation has the local analytic Cauchy–Kowalevski route on both sides. To see the remaining equations, set \(e=E_{nn},f_a=E_{na}\). With \(E_{ab}=0\), contracted Bianchi gives

\[
 e_n=-2\nabla^a f_a-2\tau e,\qquad
 (f_a)_n=\tfrac12\partial_a e-\tau f_a.
\]

The initial Gauss and Codazzi equations set \(e=f=0\); analytic uniqueness for this homogeneous normal system propagates them. Thus the conditional continuum claim is local analytic two-sided development with the original common wall and signed Israel jump. It does not imply uniform normal radius, stability of sideways integration, global periodic closure or matter/action identification.

### Numerical normal-development audit

BC takes the BB evolving source with \(\epsilon=\pm0.025\) and a zero comparator, seed lattice \(43^3\), spatial step .015, time step .006, and independently differentiates the tangential metric to reconstruct Ricci. It estimates \(F\) by a directional difference with step \(10^{-5}\). On the central \(3^3\) comparison core at \(t=.006\) the mixed wall component reaches .00163734. The one-sided \(D\) jump is at most \(1.78\,10^{-15}\) while the nonzero \(F\) jump has maximum coordinate component 30.1243. At the three normal distances, the nonzero signed cases report:

| \(|n|\) | Quadratic tangential residual | Cubic tangential residual | Cubic normal residual | Cubic mixed residual |
|---:|---:|---:|---:|---:|
| .020 | .291331 | .00780671 | .00584387 | .000119016 |
| .010 | .148941 | .00197585 | .00243826 | .000106149 |
| .005 | .0752976 | .000497002 | .00158087 | .000102472 |

All 18 selected side/amplitude/distance comparisons improve the tangential residual and preserve Lorentz signature on the comparison core. These are coordinate maxima, not invariant norms. The tangential residual is second order in normal distance in this experiment; the independent normal/mixed wall residuals (.00127626 and .000100352) expose a finite tangential discretization floor. The wall tangential residual is zero up to roundoff by construction, not independent continuum evidence. The original BB committed script is used, with its local AN metric/connection subset as in BB. BC local and committed blobs differ by a blank line only (verified Git hash after insertion). No native kernel certification or independent reproduction has been performed.

**Claim boundary and submission cut.** Include the intrinsic reduction, analytic conditional proposition and finite reproducibility table in the working draft now. Before strengthening the manuscript's headline claim: independently refine the tangential mesh and constraint residual; establish actual analytic overlap matching and controlled normal remainder/radius on exhaustion; solve the global periodic seam and physical AdS boundary conditions; distinguish the resulting spacetime from the time-symmetric AY spatial collar; and attach actual F8 causal propagation and same-source matter/action only when proved. The selected pure-tension vacuum geometry does not solve TSFV/OS, universal sourced Einstein–Israel/QFT or Monster realization. No terminal TOE or Clay promotion.


## BD — conditional periodic normal-length rigidity (26 November 2026)

The [source-specific BD audit](https://github.com/chboishabba/dashi_agda/blob/5757c105bf46b706f5af1e866f433ddc70a77e6b/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md) identifies a global matching obstruction that cannot be removed by increasing local Taylor order. This is an application of the classical normal expansion (Riccati/Raychaudhuri) equation to the original AK/AN periodic source; it is not a general nonexistence result for periodic Einstein–Israel spacetimes.

**Conditional rigidity proposition.** Assume a regular parallel Gaussian normal development on the time-reflection-fixed slice, with common oriented normal, equal vacuum cosmological constants \(\Lambda=-6\), pure constant tension jump \(j=-6/5\), and both endpoints related by the original wall matching. In \(g_5=dn^2+h\), set \(A=h^{-1}K,\ \tau=\operatorname{tr}A,\ S=A-\tau I/4,\ s=\operatorname{tr}S^2\). Reflection removes time-space blocks in adapted coordinates on that slice, making \(s\ge0\). The endpoint expansions are \(2j\) and \(-2j\). The normal vacuum equation gives \(\tau_n=4-\tau^2/4-s\). The earlier exact shear-free AK warp has \(\tau_0=4\tanh(n-\log 2)\), reaching the two endpoints at \(L_0=2\log 2\). The difference obeys \((\tau_0-\tau)_n=-(\tau_0+\tau)(\tau_0-\tau)/4+s\); thus its integrating factor is positive and the terminal difference is strictly positive if \(s\) is positive on any subinterval. Any regular connecting solution stays in \((-4,4)\) by scalar comparison at the barriers. Integrating the derivative of \(\operatorname{atanh}(\tau/4)\) yields the exact necessary length condition

\[
 \ell=2\log 2+\int_0^\ell\frac{s(n)}{4-\tau(n)^2/4}\,dn.
\]

Consequently \(\ell>L_0\) if shear is nonzero. At fixed proper parallel-normal length the shear-free tension is an upper bound on the magnitude of the allowed jump. The original coordinate period is not a proper normal length when the metric has mixed fibre components. If a global constant-thickness parallel-normal chart and the original unit fibre length are both required on the reflection-fixed spatial slice, a coordinate fibre of length \(L_0\) would contradict \(\ell>L_0\). No global chart, regularity, or parallel terminal normal is inferred from periodic topology. A changed radion, nonparallel closure or explicitly changed stress/tension remains a distinct admissible branch. Off the reflection-fixed slice \(s\) need not be positive; a purely mixed Lorentz-self-adjoint trace-free matrix gives \(s=-2\).

The [exact SymPy source checker](https://github.com/chboishabba/dashi_agda/blob/c498219ed8e15e9aa61bd95b7e8470bb39645c55/scripts/check_hopf369_p0bd.py) reconstructs the AN initial mean spatial tensor from the rational connection pullback, \(M_{\rm sp}=-\sqrt{1+|a|_\gamma^2}\,\nabla^H_{(i}a_{j)}\), including the BA temporal trace component. For both signed amplitudes \(\epsilon=\pm1/40\), at \(x=(1/5,0,0)\) the resulting \(s(0)\) is exactly \(55211989103832150835200/22954303554053101784919121>0\); at \((1/5,1/10,0)\) it is approximately .00287949, and at the origin it is zero. Zero-amplitude controls vanish. Nine exact seed controls and the comparison/warp algebra passed locally. Continuity supplies a positive shear interval for any regular continuation there, not an evaluated uniform radius or global integrated shear.

Two further reductions guide the existence problem. First, if \(V=\sqrt{|\det h|}\), then \(V_n=\tau V,\ V_{nn}=(R_h+16)V,\ (VS)_n=V\operatorname{Ric}(h)_{\rm TF}^{\rm mixed}\). Identity periodic matching requires the corresponding integrated volume and trace-free flux equations; nonidentity matching must use the actual pulled-back endpoint tensors/densities. Second, on the smooth zero-Hopf spatial cut the metric is hyperbolic four-space, so the compactly supported scalar-curvature deformation has a five-dimensional local adjoint kernel \(\nabla^2 f=f g\) (ambient hyperboloid coordinate restrictions). Its five moments must be respected by a localized linear correction. This does not contradict the earlier positive global conformal operator gap, whose domain and boundary conditions differ.

The existing V2 Cauchy majorant recipe applies to the first-order normal variables \((h,K,\partial_a h)\) with 60 independent components and four tangential directions. It gives a coefficient-dependent local analytic radius; analytic uniqueness glues common normal germs on overlaps, and finite covers give qualitative compact-subdomain radii. The actual noncompact coefficient budgets and global continuation remain unevaluated. See BD for the explicit bound and assumptions. The paper therefore retains its local analytic claim only, records the conditional fixed-length obstruction, and leaves global periodic existence, controlled numerical convergence, stress/action, F8 causal propagation and independent physical validation open. No new kernel or empirical claim.


## BE — small-amplitude global periodic initial-data construction (26 November 2026)

The [BE technical derivation](https://github.com/chboishabba/dashi_agda/blob/2c5dca8c4d562fc61d7f1690adc0d8c48115fde0/docs/c3-hopfion-abha-prior-art-maxcut-20261125.md) combines the existing AK coercive scalar transmission operator with the AY/AZ second-jet compatibility identity. It is an initial-data existence argument, not a global spacetime or a quantitative certificate at the numerical amplitude .025.

Let \(\bar g_\epsilon\) denote the original AN spatial seed, \(H,k_\pm=M\pm jH/2\) its wall data, \(S=\bar g^{yy}|_\Sigma\), and \(J_2=[\partial_n k]\). Set
\[
 f(y)=\frac{y^2(L-y)^2(L-2y)}{L^3},\qquad
 C(u)=-\frac{J_2^{\rm TF}+3j(u-1)M^{\rm TF}}{2S}.
\]
Define \(\bar g_{\epsilon,u}=\bar g_\epsilon+f C(u)_{ij}dx^idx^j\) and \(g=u^2\bar g_{\epsilon,u}\). At the seam \(f=f'=0\), \(f''(0)=2\), \(f''(L)=-2\), so the correction changes the trace-free second-normal jump by \(2SC\) while preserving the seed first junction. The fixed-tension conformal boundary equation then cancels the remaining AZ drift exactly. The scalar curvature equation supplies the trace, so \(J_{2,g}=0\) on a solution. Moreover \(g_{yy}=u^2\), \(g_{iy}/g_{yy}=a_i\): the original connection and coordinate period are unchanged, and the physical radion is allowed to vary. The physical induced wall metric is \(u_\Sigma^2H\); this family does not impose the unchanged BB wall or fixed parallel Gaussian-normal length.

**Small-amplitude proposition (classical Sobolev argument).** For each fixed integer \(m\ge5\), on the hyperbolic product cut \(H^3\times[0,L]\), use the Banach space of \(H^m\) corrections \(v=u-1\) with matching endpoint trace. The original rational Hopf pullback is \(\epsilon(1-|x|^2)\) times a smooth Euclidean covector on the closed Poincare ball; normalized hyperbolic components and all fixed-order covariant derivatives are \(O(\epsilon(1-|x|^2)^2)\), hence square integrable. The relative metric and wall jet coefficients inherit this regularity. The bulk and seam map
\[
 {\cal F}(\epsilon,v)=
 \left(-\Delta_{\bar g_{\epsilon,u}}u+
 \frac{R_{\bar g_{\epsilon,u}}}{6}u+2u^3,\,
 -[\nu_{\bar g_{\epsilon,u}}u]+j(u^2-u)\right)
\]
is smooth near \((0,0)\) into the product of \(H^{m-2}\) bulk and \(H^{m-3/2}\) wall spaces. The correction depends algebraically on \(u\), without extra derivative loss. At \(\epsilon=0\) its derivative in \(v\) vanishes identically; the linearization is the AK operator \((-\Delta+4,-[\nu\,\cdot]+j\,\cdot)\). Its quadratic form has gap \(3h_0^2\) by the AK ground-state identity, and the trace inequality yields full \(H^1\) coercivity. Lax–Milgram gives the weak inverse. Tangential spectral differentiation in \(H^3\) commutes with the warped background operator and seam; applying the energy estimate through order \(m-1\), then recovering higher normal derivatives from the bulk equation, gives the bounded inverse into the matching-trace \(H^m\) space. The Banach implicit-function theorem gives a near-reference positive solution for sufficiently small \(|\epsilon|\). On that solution the time-symmetric vacuum Hamiltonian and momentum constraints, fixed tension spatial first junction, and the full second-jet jump are satisfied globally on the spatial carrier. The requisite finite Sobolev regularity and uniform metric positivity hold by taking the neighborhood sufficiently small. An explicit Hermite interpolation of the log lapse gives the remaining selected initial temporal jump and mean-trace conditions; see BE5. This is not a proof of all higher spacetime corner conditions or of smooth/analytic time evolution.

Both [exact algebra](https://github.com/chboishabba/dashi_agda/blob/4c4f8965d5915878baf947c3681217c0daca1dae/scripts/check_hopf369_p0be.py) and [actual AN seam checks](https://github.com/chboishabba/dashi_agda/blob/00325252ef6def743effc057516a47aa7bc4b874/scripts/check_hopf369_p0be_seed.py) were executed locally; 36 signed/zero source controls with independent metric differentiation give a maximum corrected trace-free jump \(6.03\,10^{-15}\), first junction \(5.37\,10^{-15}\), and uncorrected trace-free jump up to .919 in coordinate components. These trials intentionally do not solve the scalar equation; the numerical values validate the tensor correction only. No computed global solution, evaluated amplitude threshold, independent reproduction or native kernel certificate is supplied.

The five static moments in BD remain relevant to the localized deformation route, but are not obstructions to this different global conformal/tensor family. The classical elliptic energy, implicit-function, conformal and Israel arguments are prior mathematics; the source-specific correction and its application are the present contribution. Quantitative inverse/nonlinear bounds, actual corrected solve, radion/normal-length measurement, higher junction compatibility, appropriate AdS boundary conditions and global periodic Einstein evolution remain the next proof cut. No physical matter, F8, TSFV/OS, Monster or unification claim is promoted.


### Explicit-amplitude spatial constraint proposition (BN)

The BE small-amplitude existence statement is strengthened, for the selected signed amplitudes \(\epsilon=\pm1/40\), by the [BN full-domain barrier certificate and classical existence argument](../../../docs/c3-hopfion-abha-prior-art-maxcut-20261125.md#bn--explicit-amplitude-global-scalar-constraint-by-ordered-barriers-26-november-2026). Let \(\delta=1-|x|^2\), \(\alpha=(1+|a|_\gamma^2)^{-1/2}\), \(f_0=1+(b-1)\alpha\), and \(T(w)=R(g(w))+12\) on the original BE coupled tensor family. The ordered functions
\[
w_\pm=\pm\tfrac{2}{25} f_0\delta^2
\]
satisfy the original reciprocal transmission condition and lie inside the BI uniformly elliptic positive metric region. The exact reference conformal subtraction and rational Bernstein radial jet enclosure, with outward-rounded interval evaluation, give
\[
T(w_-)/(f_0\delta^2)>0.43724,\qquad
T(w_+)/(f_0\delta^2)<-0.44424.
\]
The [compiled cover](../../../scripts/check_hopf369_p0bn_graph.py) covers 32768 cells per barrier, including the angular and radial endpoints, with no unresolved cells. The [independent replay](../../../scripts/check_hopf369_p0bn_verify.py) compares against the original coordinate BF curvature, with signed and zero controls.

Writing \(z=w/f_0\) makes the reciprocal jump condition precisely matching value and first normal derivative across the glued periodic seam. The scalar equation \(-T(f_0 z)=0\) is a uniformly elliptic divergence equation with continuous principal coefficient across that seam and a Carathéodory lower term of natural quadratic gradient growth. On each bounded solid-torus exhaustion, the ordered barriers and zero exterior Dirichlet data meet the hypotheses of Boccardo–Murat–Puel, *Résultats d'existence pour certains problèmes elliptiques quasilinéaires*, Ann. Scuola Norm. Sup. Pisa 11 (1984), 213–235, [Theorem 2.1](https://www.numdam.org/item/ASNSP_1984_4_11_2_213_0/). The BN local regularity argument uses exponential tests and weak Harnack, harmonic comparison and Campanato gradient decay, then a one-sided normal second-jet extension and linear Schauder regularity. Local compactness gives a complete-carrier solution with matching first jet of \(z\) and piecewise \(C^{2,\beta}\) regularity. The exterior weighted comparison gives \(w=O(\delta^{5/2})\) and corresponding normalized derivative decay. The full spatial \(J_2=0\) then follows from BE's exact trace-free identity and the common scalar curvature \(-12\).

This establishes classical spatial initial-data existence at the two specified nonzero amplitudes, subject to the documented interval arithmetic assumptions and classical analytic argument; the zero comparator remains exact. It does not assert an amplitude interval, a computed exact representative, membership of this solution in BM's small derivative neighborhood, global uniqueness, native kernel certification, analytic higher-corner compatibility, physical-time Einstein evolution or a physical validation. The original connection, tension and coordinate period remain unchanged, and the proper fibre length is bounded between \(L/(1+.08\delta^2)\) and \(L/(1-.08\delta^2)\); the Gaussian-normal distance is a different quantity. BE lapse data and BA/BB/BC evolution are the next consumer, not an automatic consequence of this spatial proposition.


### Reduced evolution frontier: fixed-material F scale channel (BR96–119)

The [reconciled closure roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md)
retains the original signed BN/BE/BO/BQ geometry. A third candidate
boundary allocation F imposes all five geometric gauge jumps and
retains the mean-force equation. The gauge subsidiary uniqueness
argument uses continuous traces and a signed Robin potential,
conditional on a given regular reduced development with compatible
initial/exterior data. Neither a full variable metric energy nor
that reduced development has been established.

For the original zero-Hopf AK harmonic-Y reference, the exact
linearized normal-scale equation at the BR14 base RNC point is
\[
(\Box_g-6k n-8)\ell=2k\,\delta C_\perp-\delta E_{\mathrm{red},nn},
\qquad n\ell-4k\ell=\delta C_\perp\quad\text{at the F seam}.
\]
Here \(\ell=\delta\log\lambda\) is a metric perturbation (not the
normal spectral root). The optical conjugation gives a scalar
potential between \(104/25\) and \(731/100\); a conservative
frozen Robin spectral lower bound is \(-17\), and the damped
scalar resolvent is bounded by \(1/239\) at damping at least
16. The [BR116–119 source checks](../../../scripts/check_hopf369_br116_119_F_structured_scale.py)
independently compare the normal reduced Ricci component and
retain nonzero gauge and reduced defects. No general tangential
chart or nonzero Hopf estimate follows from this reference calculation.

The general shape-source variation retains the term
\(-2\operatorname{tr}(S\,\delta A)\), with \(A=h^{-1}K\) and
\(S=A-\operatorname{tr}(A)I/4\). Exact differentiation of the
original AN seed at \((1/5,0,0)\), \(\epsilon=1/40\), gives
a nonzero mean spatial shear minor, which is preserved by
positive conformal scaling and the first-jet-preserving BE/BO/BQ
repairs. Thus the reference cancellation cannot be carried over
unchanged. Full foliation transport cancels the pure Lie shape
term but also changes the scale-jump channel; the corresponding
chart transmission and nonlinear energy remain open. These are
source-specific algebraic and conditional frozen results, not
proof of physical spacetime development or validation.


### Source-jump inverse and transported shear qualification (BR120–123)

At a matched continuous full metric, the normal derivative jump is determined uniquely by the ten geometric Israel rows and five contracted harmonic-source rows, with the actual source jump retained. For constant pure tension and common geometric gauge, the derivative jump in a graph chart is \(J=\lambda(2jg+6j\,n^\flat\otimes n^\flat+n^\flat\otimes[H]+[H]\otimes n^\flat)\). A linearized F scale jump can be transferred to a moving continuous-metric jet by subtracting a common-value Lie generator with the prescribed normal derivative jump; its graph displacement must be retained. This is a conditional jet equivalence, not a variable-coefficient chart existence theorem. The scalar-vector wave commutator identifies the pure-coordinate shear term, but a nonzero null mixed polarization satisfying the principal gauge, trace and Codazzi conditions still has nonzero shear pairing. Full curved Gauss/Weyl conditions, vector transmission, higher regularity and coupled evolution remain necessary. See [BR120–123 roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md#15-br120123--arbitrary-source-jump-moving-chart-bidi-commutator-and-constrained-shear) and [local source checks](../../../scripts/check_hopf369_br120_123_F_source_transport.py). Classical geometry and commutator identities retain prior attribution. No full PDE acceptance is inferred.


### Full Gauss and electric-Weyl mean-shape inverse (BR124–127)

On a matched timelike pure-tension wall with constant nonzero tension parameter \(j\), write \(M=\operatorname{mean}K\), \(\operatorname{tr}_h M=0\), and \(D=\operatorname{Ric}+4g\). The scalar Gauss average is \(R_h=-12+3j^2-\operatorname{tr}((h^{-1}M)^2)+\operatorname{mean}(\operatorname{tr}_hD_\parallel-D_{nn})\). Its full material variation pays the scalar mean-shape contraction only if the intrinsic curvature and Ricci defect are controlled. The full Weyl jump factors through the single effective trace-free shape \(M_{\mathrm{eff}}=M+\operatorname{tf}_h[D_\parallel]/(3j)\), with electric jump \([W_{nanb}]=2j(M_{\mathrm{eff}})_{ab}\). Thus geometric mean shape is recovered algebraically when the defect is known; zero Weyl jump alone cannot exclude nonzero shape in a reduced metric with nonzero Ricci defect. In the original BR29 carrier the active and zero-speed normal projections have ranks eight and six on the shape, jointly rank nine. Both are required for the full inverse. A local Gaussian normal Riccati variation propagates shape from its boundary value and electric Riemann source, retaining noncommuting coefficients and homogeneous holonomy. This is not an actual constrained curvature-trace estimate, weighted global reconstruction or nonlinear spacetime existence theorem. See [BR124–127 roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md) and [local exact checks](../../../scripts/check_hopf369_br124_127_F_gauss_weyl.py). Classical Gauss/Weyl/Riccati identities retain prior attribution.


### Same-metric curvature preservation and material energy (BR128–131)

In the original BR29 orthonormal leaf frame, multiplying the projected bulk equation by the material normal lapse makes its normal principal matrix constant. Tangential commutators then contain only tangential derivatives at the principal level. For the actual Ricci defect \(D=\mathrm{Ric}+4g\), the effective mean shape \(M+\mathrm{tf}_h[D_\parallel]/(3j)\) absorbs the derivative-jump correction into the wall forcing. The existing signed curvature/wall work identity gives a positive coupled energy on a given regular compact material chart, with uniform time coercivity, compatible jets and controlled exterior flux. In particular, a sufficiently regular projected solution with the same given metric, actual Cotton/Codazzi sources, geometric initial data and exterior conditions is unique against the geometric Weyl/shape pair. This conditional statement does not construct the metric or its global exterior. The material normal Riccati equation contains the lapse-Hessian term \(-\lambda^{-1}(\mathrm{Hess}_h\lambda)^\sharp\); its linearized inverse retains the transported holonomy moment and normal/frame variations. Temporal Cartan connection/coframe evolution supplies a separate nonlinear construction route with explicit curvature and torsion defect equations, conditional on full unprojected Bianchi and wall compatibility. The projected curvature estimate alone does not establish these conditions on an unknown metric. See [BR128–131 roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md) and [local checks](../../../scripts/check_hopf369_br128_131_F_curvature_development.py). Classical curvature, energy and Cartan identities retain prior attribution; no nonlinear existence or native promotion.


### Reference subsidiary work and covariant Cartan defect attachment (BR132–135)

The earlier rank-twelve subsidiary work obstruction applied to the selected eleven-row wall source. Restoring all twelve time-evolution rows of the actual eleven-coordinate cyclic wall Codazzi residual gives an exact work multiplier, without adding an independent wall mode. Its tangential skew is paid by the spatial Bianchi identity: in the spatial Hodge variables \(e,X\) with \(\operatorname{tr}X=0\), the skew work is \(-3e\cdot\operatorname{div}_T X/2\); the actual flat principal compatibility gives \(\operatorname{div}_T X=2\partial_t e\). The corrected positive quadratic wall mass is \(9|e|^2/2+3\|X_{\rm sym}\|^2+6\|X_{\rm skew}\|^2\), multiplied by the positive \(-j\). This resolves the normal/tangential work algebra for the extended flat principal bulk and symmetric reference seam on compatible derivatives, not the full curved variable-coefficient evolution. The rank-ten bulk graph discrepancy factors through the spatial exterior derivative of the magnetic Bianchi residual. For an independent connection with curvature defect \(E=F_\Omega-R\), the exterior residuals \(C=D_\Omega R\) and \(D=D_\Omega(*R)\) satisfy \(D_\Omega C=[E,R]\), \(D_\Omega D=[E,*R]\). The covariant wall Codazzi curl, with matched intrinsic connection and shape, retains the tangential Cartan curvature defect through \(D_\omega H=\operatorname{mean}(D_\Omega R)_{nt}+\operatorname{mean}(\Omega_{nt}\wedge E_{\parallel})\). These exact source identities support the next variable Cartan subsidiary estimate, but do not assert torsion/frame conversion, nonlinear existence, exterior regularity or native acceptance. See [BR132–135 roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md) and [local exact checks](../../../scripts/check_hopf369_br132_135_F_bianchi_cartan.py). Classical Bianchi/Cartan identities retain prior attribution.


### Nonzero mean subsidiary work and local compatible current (BR136–139)

In the original BR29 constraint graph, the quadratic mean-shape term in the differentiated full Israel Weyl jump is not zero: six selected residual entries remain nonzero polynomials. Its active and signed normal-work projections vanish identically, as does the corresponding raw wall magnetic exchange. Thus the earlier reference extrinsic work cancellation extends to arbitrary trace-free mean shape under the stated matched-frame, full-jump and vacuum-source hypotheses. The BR133 compatible wall skew correction gives a local symmetric flux current with positive mass and exact flux-relative speeds \(0,\pm1/3,\pm1/2\); rotational covariance gives its bound in every spatial direction. This yields positive time mass on tilted timelike slices, without claiming a free-jet symmetrizer or physical propagation speeds. For independent metric-compatible connection and coframe, the exterior derivative differs from the alternating frame derivative by \(\sum_a T^a\wedge\iota_{e_a}F\), for both \(R\) and \(*R\); torsion cannot be dropped off shell. The Cartan spatial identity gives the normal derivative of the wall curvature-defect pullback from the exterior Bianchi residual, connection work and one tangential derivative of the mixed defect. Its explicit trace budget does not close a same-order combined energy, and bulk \(L^2\) alone cannot control that trace. The actual intrinsic/frame and surface-defect evolution, nonlinear tame estimate, exterior/holonomy and development remain necessary. See [BR136–139 roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md) and [local checks](../../../scripts/check_hopf369_br136_139_F_variable_subsidiary.py). Classical differential geometry and trace identities retain prior attribution.


### Parallel physical readout and Cartan trace quotient (BR143–145)

The noncompact G3 branch has an initial tidal observation independent
of the periodic wall theorem. At the original radial centre with
\(p=\psi(0)\) and the signed oriented horizontal/fibre orthonormal
frame, the actual time-symmetric vacuum electric curvature is
\[
T_5=p^{-2}
\begin{pmatrix}
-208\epsilon^2/9&0&0&0\\
0&-208\epsilon^2/9&0&0\\
0&0&80\epsilon^2/9&16\epsilon\\
0&0&16\epsilon&112\epsilon^2/3
\end{pmatrix}.
\]
Its trace vanishes. The longitudinal/fibre block has negative
determinant for \(0<\epsilon^2<27/35\), including the original
\(\epsilon=1/4\). Relative geodesic acceleration is \(-T_5\)
in the stated curvature convention. The same radial solution at
opposite field amplitude gives the same diagonal blocks and spectrum
but opposite oriented mixed component. Thus the signed amplitude
is recovered by \(p^2T_{z5}/16\) on this two-state fibre, whereas
the coarse diagonal/spectral observer is insufficient. Fibre reflection
relates the unoriented metrics; no absolute measurable sign or
four-dimensional detector prediction follows. This is a local
dimensionless initial observation under the P0T/U analytic assumptions,
not a calibrated trajectory or quantum equivalence.

For the periodic branch BR143 independently reconstructs the BR29
residual graph and finds the 30-row electric trace has rank 23,
with rank four on the kernel of the rank-22 normal-work form.
Its nine-slot spatial restriction has rank three and annihilates
that kernel, so factors through the normal-work matrix. This is
not a bound by the indefinite scalar flux or a proof of trace
regularity. The full curved/torsionful surface estimate and W6
remain open. The native TOE adapter now consumes the existing
consumer non-descent witness at rational sign-fibre scope.
Three local exact stages PASS; no native kernel, PDE or physical
calibration acceptance. See [parallel dependency register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Actual central light screen, matter tidal trace and joint signed readout (BR146–149)

On the original G3 circle-invariant local vacuum development, a
five-dimensional null geodesic with zero conserved fibre momentum
projects to a null geodesic of the Jordan/base metric. Nonzero
fibre momentum instead gives a timelike projection. At the initial
centre with \(p=\psi(0)\), the optical tidal screen of the zero-momentum
null direction at angle \(\theta\) from the original axis is
\(\epsilon^2 p^{-2}\operatorname{diag}(-176/9,-176/9+32\sin^2\theta)\).
Its trace is \(-\epsilon^2p^{-2}(64/9+32\cos^2\theta)\), independently
recovered from the reduced radion and connection equations. This
is a local Jordan-frame geometric optical result, not physical
Maxwell photon identification, negative matter or global lensing.
For an initially comoving normal Jacobi field in the marked
five-dimensional frame the leading mixed map is
\(J_{5z}=-8\epsilon t^2/p^2+O(t^4)\) under the time-reflection
and analytic development assumptions. A certified finite-time
remainder and actual detector coupling remain necessary.

For the separate G4 Einstein–ideal-RMHD initial source with
\(\rho=K_0-p_0+b^2\), actual aligned total stress has
\(S_\parallel-S_\perp=j^2/(S_f+p_{\rm fluid})-b^2\le0\),
strict for nonzero magnetic field and \(\psi>1\) in the admitted
smallness range. The actual electric curvature is
\(\mathrm{Ric}(\gamma)+K_{\rm tr}K-K^2
-\kappa(S+(\rho-\operatorname{tr}S)I/2)\), with trace
\(\kappa(K_0+2b^2+2p_{\rm fluid})/2>0\). Its tracefree spatial
curvature and extrinsic data are retained; a stress formula
does not independently determine the full tidal matrix.

The paired G3 readout \(q=-9\,\mathrm{Ric}_4(k,k)|_{\theta=\pi/2}/64\)
and \(m=T_{z5}/16\) gives \(\epsilon=q/m,\ p^2=q/m^2\)
off zero. At zero both observations vanish and the source
boundary condition, not division, selects the original radius.
This is a selected marked observer BIDI, not a full dynamical
or quantum equivalence. BR146 shows that the full periodic
electric trace factors through the extended normal action of
rank 26, whose kernel dimension is nine, rather than only the
compressed normal-work rank22. The apparent four blind directions
are normal-active. The one-sided trace bound still requires a
tangential jet at top order and actual off-shell graph conversion.
Four local exact stages passed, no native or nonlinear acceptance.
See [BR146–149 register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Frame-indexed optics, actual York source and literal Leech order-three control (BR150–153)

The original G3 Jordan optical screen is not invariant under
the Einstein-frame metric choice. For \(g_E=\phi g_J\) at the
time-symmetric central event, the actual radion Hessian cancels
the common negative Jordan contribution, giving
\(\mathcal O_E=\epsilon^2p^{-3}\operatorname{diag}(0,32\sin^2\theta)\).
This is independently consistent with the Einstein-frame vacuum
circle reduction null Ricci equation. Physical detector coupling,
affine normalization and metric choice must therefore be specified;
no negative-mass or gravity-manipulation conclusion follows.
The normalized transverse Einstein trace \(q_E=\epsilon^2/p^3\)
and oriented mixed five-dimensional probe \(m=\epsilon/p^2\)
recover \(p=q_E/m^2,\epsilon=mp^2\) off zero. Conditional on
actual uniform tidal bounds \(K=\sup\|T\|\), \(M_2=\sup\|T''\|\)
and reflection symmetry, the normal Jacobi error is bounded by
\(t^4(M_2+K^2\cosh(\sqrt K |t|))/24\); actual constants and
lifespan remain unpaid. The original \(\epsilon=1/4\) central
radial normalization satisfies \(19/18\le p\le18/17\).

For the independent G4 matter source, the original Fourier
York tensor has an explicit regular radial-angular inverse
Laplacian expression. Its central value is zero and its
gradient is
\(\partial_lY_{ij}=a[12(\delta_{li}z_j+\delta_{lj}z_i)/5
-8\delta_{ij}z_l/5]\), \(a=\kappa s\alpha\), independently
recovered from angular Fourier moments. The actual conformal
Hessian is axial, not assumed radial. Its trace is fixed by
the central Hamiltonian; its single remaining anisotropy is
an explicit convergent Newton quadrupole integral on the
same nonlinear contraction solution. The full electric
tidal difference is \(-2(H_z-H_x)/p^4-\kappa(S_\parallel-S_\perp)\).
The integral is not yet evaluated numerically.

The extended periodic normal trace has a half-order mixed
tangential Sobolev budget, not an unconditional same-order
surface estimate. The literal P0AO Leech code admits the
fixed-free order-three projective-line permutation tested in
BR153. The corrected selected central-extension lift has
ground character \(16\), and selected weight-two tensor/pair
character zero, excluding this actor as the target 3B
character \(54\). This is a source-specific finite negative
control, not a canonical FLM or Monster class identification.
Four local stages passed; no native kernel, full PDE or
physical calibration acceptance. See
[BR150–153 dependency and proof register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Atomic and periodic-table source handoff (BR154–156)

The original atomic programme (#886) already supplies the typed
369-to-orbital, fermion, interacting-energy and periodic-table
construction, with H/He physical benchmark receipts. The actual
n=2 shell has eight spin-orbitals (2s and 2p, including spin);
three such carriers fit the punctured-nine 24D address chart,
but their orbital-only C3 action has trace 2 per shell, not
the free-lane character. A selected combined finite KK lane
and orbital rotation \(G=K\otimes B\) is conjugate by
\(J=\operatorname{diag}(I,B,B^2)\) to \(K\otimes I\),
with an exact selected-mode Hamiltonian intertwiner including
s/p splitting. The independent physical matter action and
detector coupling remain unpaid. On the original projected
hydrogenic 2p² Coulomb source, retaining all spin-orbitals gives
15 antisymmetric states and energies \(21/128,237/1280,111/512\)
with multiplicities 9,5,1 respectively in atomic units.
The physical magnetic rotation commutes with this interaction,
whereas the bare cyclic magnetic label shift has rank-two
commutator on the full projected carrier; the previous
common-spin scalar block hid this residual. This finite
interacting operator is not a full atomic spectrum or
a quantum gravity equivalence. The original atomic clock,
crystal and matter source owners are now explicitly linked
in [the canonical roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Atomic angular action, matter coupling and leading G4 anisotropy (BR157–160)

On the original 15-dimensional spin-orbital \(2p^2\) projection,
the actual angular projectors \(P=S^2/2\), \(D=(L^2-2P)/6\)
and \(Z=I-P-D\) have ranks 9, 5 and 1 and exactly reconstruct
the selected Coulomb operator. For the supplied spin-orbit
coefficient \(\zeta\), the sum of one-particle \(l\cdot s\) operators
preserves total \(J\), with \(J=0,1,2\) blocks of dimensions
2,3,10; it does not preserve total \(L^2\). The reduced
polynomial equations are verified in the executable checker.
Averaging the cyclic magnetic-label action erases the original
term splitting, but the signed orbit residuals have a common
three-dimensional invariant support. This is an exact
source-specific BIDI operator decomposition, not a symmetry
of the fixed interacting Hamiltonian.

A selected local bulk zero-mode Dirac and independent Maxwell
Coulomb model gives \(m_E\propto f^{-1/2}\), \(\alpha\propto f^{-1}\),
and hence \(\Delta E_E\propto f^{-5/2}\),
\(\Delta E_J\propto f^{-2}\), where \(f=\phi/\phi_{\rm ref}\).
The proper-time phase is frame invariant for the same chosen
matter action. An independently chosen Jordan-minimal brane
clock has different radion response. The initial G3 radion
contribution to the bulk-model gap ratio has second normal-time
derivative \(224\epsilon^2/(3p^2)\); curvature, Pauli, gradient,
nuclear and detector corrections are not included. No measured
clock signal or full physical matter action is claimed.

The original G4 York source yields a leading central log-Hessian
difference \(H_z-H_x=(a^2/20)I_Y+O(\epsilon^4)\), with
\(a^2=\kappa^2K_0\epsilon^2\) and \(I_Y=\int_0^\infty V_2(r)dr/r\).
Here \(V_2=-2A^2+6C^2-2D^2\) is the actual angular norm coefficient
of BR152. The reproducible truncated high-precision quadrature
is approximately 1.11300325163; an outward interval certificate
and the actual nonlinear finite-amplitude quadrupole remain
open. The corresponding leading tidal difference is
\(-a^2 I_Y/10+O(\epsilon^4)\), not a certified finite-amplitude
sign. See [BR157–160 in the roadmap](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Exact G4 anisotropy, selected atomic Pauli term and covariant Bianchi source (BR161–164)

The original York quadrupole has the closed form
\(I_Y=2224/3-75\pi^2\), with exact rational enclosure
\(1.113<I_Y<1.114\). An explicit Newton-gradient/source-error
budget gives a sufficient finite-amplitude bound for the
central tidal difference. For the chosen normalized admitted
G4 parameters \(\kappa=K_0=1,p_0=1/4,\epsilon=1/2000\),
the full initial \(T_{zz}-T_{xx}\) is bounded above by
\(-117169089470921/6124902000000000000000\).
This is an analytical consequence of the original contraction
solution under its hypotheses; no numerical nonlinear profile,
evolved spacetime or calibrated parameter claim is made.

The actual p² singlet projectors \(Z_k\) form an orthogonal
three-element orbit on the BR158 invariant support \(Q_E\);
with \(\delta=81/2560\), the interaction residual is exactly
\(R_k=\delta(Z_k-Q_E/3)\). Reopening is lossless. The
selected hydrogenic 2p radial Pauli coefficient is
\(\zeta=\alpha_{\rm EM}^2Z^4/48\) in atomic units. In the
selected bulk matter model the leading Pauli and Coulomb
Jordan-time gap weights differ (\(f^{-4}\) versus \(f^{-2}\)).
Neither the full interacting Breit–Pauli operator nor the
actual KK spin connection is included.

For the periodic branch, use the covariant alternating
operator \(A=\mathrm{Alt}\nabla\) on all tensor slots rather
than the exterior residual. Its square on the target
algebraic curvature and its Hodge dual is a homogeneous
source in connection curvature error and torsion times
first target derivatives, without differentiated torsion.
The actual BR132/143 rank-10 compatibility factorization
is replayed and gives a route to an extended symmetric
bulk subsidiary equation on a given regular frame. The
curved surface trace and nonlinear coupled existence are
still unpaid. Four local stages PASS; no native, full
runner, physical trajectory or empirical acceptance.
See [the controlling proof register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Actual cylinder spin connection and extended gravitational sign region (BR165–168)

The exact original BR27 Weyl donor is byte-verified and
replayed; its embedding and four compressed symbols agree
with BR143. This does not replay all BR128–139 stages or
settle the coupled periodic wall trace. On the original
circle-invariant G3 metric, let \(\theta^5=\phi(dy+A)\).
The torsion-free connection has
\(\Omega_{5a}=v_a\theta^5+(\phi/2)F_{ab}\theta^b\) and
\(\Omega_{ab}=\omega_{ab}-(\phi/2)F_{ab}\theta^5\).
With the stated Clifford convention, the radius-normalized
periodic zero-mode Dirac operator contains the actual
geometric Pauli term \((\phi/8)\Gamma^5F_{ab}\Gamma^a\Gamma^b\)
in addition to the base operator and supplied mass.
It survives at zero compact momentum. The independent
physical Maxwell field is distinct from this connection.
At the G3 centre the geometric term has coefficient
\(b=2\epsilon/p\) multiplying \(\Gamma^5\Gamma^1\Gamma^2\).
For the local frozen free symbol its dispersion is
\(E_\pm^2=m^2+k_z^2+(k_\perp\pm b)^2\), so the unlabelled
spectrum forgets the sign and the rest energy is
\(\sqrt{m^2+b^2}\), not a linear rest splitting.
Actual bound-state spectroscopy, field variation,
spin structure, test-matter validity and measurement
calibration must still be paid. This is not a complete
Einstein–Dirac–Maxwell solution.

BR161's conservative sufficient G4 sign budget extends
uniformly at \(\kappa=K_0=1,p_0=1/4\) to all
\(0<|\epsilon|\le1/1200\). The exact rational inequality
at the upper endpoint gives a negative upper coefficient
for \((T_{zz}-T_{xx})/\epsilon^2\) (approximately
\(-0.0146882278804\)); monotonicity covers the smaller
amplitudes. This concerns original nonlinear constrained
initial data, not evolved trajectories or measured units.
Four local exact stages passed plus the BR27 standalone
replay. See [the controlling register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Selected spatial Hopf spinor interaction and compatible grazing trace (BR169–171)

The original KK Dirac odd block has \(D_+=-i\sigma\cdot p
-\sigma\cdot b(x)\), with its adjoint as lower block.
Its positive-mass square is
\(p^2+|b|^2+\operatorname{div}b+
\sigma\cdot(2b\times p+i\operatorname{curl}b)\).
At the initial G3 slice the actual linear source is
\(b=\epsilon B_0/4\), divergence-free. On the complete
hydrogenic \(n=2\) spin-orbital projection the leading
Pauli perturbation includes both \(2s\)-\(2p\) and
\(2p\)-\(2p\) blocks. With inverse Bohr scale \(\lambda\)
in source units, their coefficients are
\(a=\epsilon\lambda^5(12m)^{-1}\int_0^\infty
r^5e^{-\lambda r}(1+r^2)^{-3}dr\) and the analogous
\(c\) with \(r^4\). Both have the sign of \(\epsilon\).
The exact polynomial is
\(E^4(E^2-2a^2-2c^2)^2\), a signed triad of
multiplicities \(2,4,2\) at nonzero amplitude.
The sign exchanges the two nonzero spectral projectors,
not the unordered spectrum. This is a selected leading
nonrelativistic degenerate-shell perturbation, not a
calibrated transition or a complete curved Dirac
spectrum. Actual fine structure and interactions must
be combined at the matrix level.

The periodic flat-principal Weyl half-speed modes have
nonzero restricted spatial electric trace of rank two
on each eight-dimensional actual constraint image.
The written grazing wave-packet argument excludes
a same-order trace bound from uncoupled bulk evolution
alone, not from the coupled Israel wall problem.
The exact BR128–131 source replay passed using the
byte-identical original BR27 donor. BR132–139 replay,
joint boundary-symbol estimates and nonlinear
generation remain. Three new exact stages passed;
no kernel, full PDE or empirical acceptance.
See [the controlling register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Joint selected atomic fine structure and wall-compatible half-speed branch (BR172–174)

Adding the selected \(s/p\) energies and central one-electron
spin-orbit term directly to BR170's eight-state Hopf matrix
preserves axial \(J_z\) and a Kramers antiunitary on this
initial projected operator. The exact characteristic
polynomial is
\[
 (x-E_p-\zeta/2)^2
 \big[(x-E_s)((x-E_p+\zeta/2)(x-E_p)-2c^2-\zeta^2/2)
       -2a^2(x-E_p)\big]^2.
\]
The cubic determines \(a^2,c^2\) individually off \(E_s=E_p\)
for known baseline coefficients; at degeneracy it retains
only their sum. The marked matrix blocks restore the sign,
whereas even the combined energy spectrum forgets it.
This is a selected atomic model, not a measured spectrum
or the full interacting curved Dirac dynamics.

For the frozen reference periodic bulk/shape system with
common Weyl value and zero shape perturbation, the actual
constraint \(Rw=0\) leaves five exactly tangential half-speed
directions at each sign, with spatial trace rank two.
At three nonzero rational tilts the \(+1/2\) subspace has
rank-seven wall-source restriction. A symbolic continuing
mode satisfies \(A(\theta)w=w/2,\ Rw=0\) and exact spatial
trace norm ratio \(\sin^2\theta\cos^2\theta/12\). This supplies
normal-angle suppression for that selected branch, not for
all glancing modes. The full nonzero-shape joint boundary
pencil and curved Cartan conditions remain open. BR132–139
dependent replay remains unpaid. Three local stages passed,
no native kernel, nonlinear evolution or empirical acceptance.
See [the proof register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Reference reflection sectors, paired grazing obstruction and radial inverse (BR175–177)

The actual frozen Weyl/shape wall problem admits an exact
normal-reflection split. With \(F\) the original signed
normal-index reflection and \(P_\pm=(I\pm F)/2\), reflecting
the minus-side field and taking its sum/difference with
the plus-side field gives sectors \(a,b\) with boundary
conditions \(P_-a=0,\ P_+b=jJm/2\) and wall equation
\(m_t=\sum B_i\partial_i m-Rb\). This retains nonzero shape
and the original work cancellation. It is a reference
bulk/shape identity, not full curved well-posedness.
Pairs of opposite normal Fourier waves on the half-speed
and stationary branches satisfy the reflection-even
reference wall condition with zero shape and vanishing
selected mixed magnetic readout, but their spatial
electric traces are proportional to \(\cos\theta\) and
\(\cos^2\theta\), respectively, not suppressed at grazing.
The written periodic Fourier constructions give trace
growth \(k^{1/4}\) and \(k^{1/2}\) at bounded bulk residual
norm. The stationary branch therefore also obstructs
a simple time-integration remedy in this reference
subsystem. The actual curved tangential Cartan constraints
and derivative-balanced weighted surface energy remain
necessary; these are not counterexamples to the full
Einstein–Israel IBVP.

For the selected atomic radial source, the ratio of the
two original Hopf coefficients is the mean radius
\(\rho(\lambda)=I_1/I_0\) with positive weight
\(r^4e^{-\lambda r}/(1+r^2)^3\).
Its derivative is minus the strict radial variance.
The endpoint limits are infinity at \(\lambda\downarrow0\)
and zero at \(\lambda\uparrow\infty\), so the ratio uniquely
recovers the inverse Bohr scale within this selected
model. With known nondegenerate baseline and mass the
two spectral magnitudes then determine amplitude
magnitude and the marked matrix restores its sign.
At baseline degeneracy the independent radial scale
must be known to recover amplitude magnitude from the
combined norm. The zero fibre remains non-identifiable
from the vanishing interaction. No physical calibration
or complete atomic spectrum is claimed.

All eight original BR132–139 dependent stages now replay
successfully on byte-identical committed sources, resolving
the earlier donor provenance limitation for BR128–139.
Three new exact stages passed. No native kernel, integrated
runner, nonlinear evolution or empirical acceptance.
See [the proof register](../../../docs/hopf369-geometry-forward-closure-reconciled-20261128.md).


### Terminal source geometry (BR178–201, source-written)

The homogeneous full exterior symbol of Ricci-free algebraic
curvature is injective for non-null covectors. The spatial inverse
uses the exact full exterior matrix and its image projector;
the complementary incompatible source is retained. BR197 writes
a direct test of the null kernel against the original projected
characteristic carrier, retaining five physical polarizations
per null sign. These tests are pending local replay and do not
provide curved bulk-boundary estimates.

The selected atomic 28-state n=2 projection now has all hydrogenic
2s/2p Coulomb channels written with Gaunt angular coefficients and
the original BR172 marked one-body operator. No beyond-shell
CI, calibration or physical spectrum is claimed. The radial
majorant and complex graph bounds give conditional initial
analytic coefficient control. The marked central tidal readouts
u=epsilon/p² and v=epsilon²/p² invert both parameters away from
zero; the zero observation cannot recover p. G4 primitive
discriminant and enthalpy bounds are conditional continuation
guards, not an actual evolution proof.

The native marked chart cube has six written proof bodies;
physical time/history attachment is open. The material
comparator remains a finite prescribed metric/shift history.
The complete W0–W7 nonlinear theorem, native kernel and
BR178–201 local replay remain open. See the controlling register
for all seven parallel lanes.

### BR211–212 physical boundary pencil

The original static complex-null Weyl/Israel jump is injective, but a regular five-polarization chart at glancing reveals rank 13 rather than 19. Adding the original wall evolution rows yields rank 15 at both glancing signs for three tested tangential frequencies. A factored minor proves injectivity on the real parametrized open oscillatory arc; its seventh-order vanishing is not a sharp inverse-loss bound. Local independent exact checks passed; original donor import, damped complex-frequency bounds and curved existence remain open. See roadmap section 47.

### BR213 local glancing elementary divisors

Exact truncated coefficient-map ranks on both glancing signs at k=1,2,10 give elementary orders (0^13,1^5,2) for the jump and (0^15,1^4) for the joint jump/wall system. Thus the local inverse loss for the coupled physical system is first order in the glancing normal parameter at these fixed frequencies. Uniform high-frequency constants, compatible sources and curved transfer remain open. See roadmap section 48.

### BR214 compactified frequency

With wall rows divided by k and h=1/k, symbolic maximal minors establish first-order local coupled elementary divisors for every finite positive k. At h=0 the jump-only second-order direction returns. A product-neighborhood uniform first-order inverse in these normalized norms is therefore excluded; the damped physical ray and compatible source weights still need a two-parameter estimate. See roadmap section 49.
