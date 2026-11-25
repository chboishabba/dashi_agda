# C3 / 369 Hopfion, ABHA and torus-knot prior-art ledger — 2026-11-25

## Source ownership and evidence levels
The supplied @vortex_math screenshot reproduces Kobayashi–Nitta Figure 4 (arXiv:1304.6021 v2 PDF p4), including panel labels, green n3=0 and blue n1=-0.97 isosurfaces. Original source https://arxiv.org/pdf/1304.6021 ; first submission 2013-04-22 https://arxiv.org/abs/1304.6021 ; DOI 10.1016/j.physletb.2013.12.002. PDF pp4–5 visually inspected. The authors solve a classical extended Faddeev–Skyrme model numerically; no quark detection. Personal priority investigation retired by user direction; original scientific and independent Rodin/ABHA source records remain in scope.

### Earlier primary mathematical and physical owners
- Gladikowski and Hellmund, 1996-09-03, https://arxiv.org/abs/hep-th/9609035 : O(3) Hopf solitons, numerical charges 1,2; cites Faddeev's 1975 proposal and 1979 Vakulenko–Kapitanskii bound. Not a quark model.
- Faddeev and Niemi, 1996-10-24, https://arxiv.org/abs/hep-th/9610193 ; Nature 1997 DOI 10.1038/387058a0 : numerical indications of unknot/trefoil solitons and conjecture of all torus knots. https://arxiv.org/abs/hep-th/9705176 (1997-05-22) investigates toroidal unknot.
- Battye and Sutcliffe, 1998-11-30, DOI 10.1103/PhysRevLett.81.4798 : numerical knots/links through Hopf charge 8; standard FS trefoil charge 7.
- Aratyn, Ferreira and Zimerman, 1999-05-11, https://arxiv.org/abs/hep-th/9905079 ; DOI 10.1103/PhysRevLett.83.1723 : exact toroidal static solitons in a DIFFERENT integrable theory, two integer labels whose product is Hopf charge. https://arxiv.org/abs/hep-th/9902141 earlier unit-charge solution.
- Hietarinta and Salo, 1999, DOI 10.1016/S0370-2693(99)00054-4 : linked unknot relaxation depends on relative handedness/direction.
- Finkelstein, 2004-08-27, https://arxiv.org/abs/hep-th/0408218 ; Finkelstein and Cadavid 2005-07-01 https://arxiv.org/abs/hep-th/0507022 : speculative quantum-group trefoil model of fermions, explicitly quarks and leptons. Not empirically established.
- Bilson-Thompson, 2005-03-22, https://arxiv.org/abs/hep-ph/0503213 : B3 framed preon braid candidate for quarks, leptons and gauge bosons; not a confirmed substructure.
- Sutcliffe, 2007-05-10, https://arxiv.org/abs/0705.1468 : rational maps S3 -> CP1 supply initial torus-knot configurations and numerical FS solutions up to Hopf charge 16. Not the later domain-wall kink construction.
- Kobayashi and Nitta, 2013-04-17, https://arxiv.org/abs/1304.4737 : quadratic-potential toroidal domain walls with P,Q in 1,2,3, C=PQ. 2013-04-22 paper adds linear potential, distinguishes kink curves and stability: (3,2) stable in their numerical search, (2,3) and (2,2) not found; not a universal nonexistence proof.

### Independent Rodin / ABHA lineage
- Russell P Blake, https://www.rexresearch.com/rodin/6-blakemathformulation.pdf : explicit attempt at modulo-nine formalization, hosted copy associated with 2007 project filename, exact original publication date not established.
- Marko Rodin and Greg Volk, 2010 NPA proceedings, https://www.rexresearch.com/rodin/3-numbermapcoil.pdf ; p6 Figure 2 and Table 9 visually inspected. Explicit twisted periodic map, three circuits connected by column shift not divisible by three, opposite current directions, 396693 gap pattern and recommended 12 poloidal / 5 toroidal turns. This is actual discrete and winding formalization, not the same FS action, not a quark model; text search no quark. Conclusion acknowledges absence of controlled quantitative studies at publication.
- Randy Powell 2010-04-14 https://www.youtube.com/watch?v=7pvuTZ5u6Kg : dated public ABHA presentation; 2012-11-08 https://redice.tv/red-ice-radio/vortex-based-mathematics-and-the-abha-torus : public interview. 
- Russell Gries https://www.scribd.com/document/54220752/Russell-Gries-s-Perspective-on-the-Activation-Sequence-of-the-ABHA-Torus-Using-Electricity : 9x9 grid, three 120-degree phase sequences; hosting timestamp not proof of original creation date.
- 2010-12-28 visualization https://www.galacticresonance.org/36x36-abha-torus-firing-sequence-this-is-the/ ; 2012 Wikimedia video https://commons.wikimedia.org/wiki/File:Web_3D_ABHA_Torus_-_UPDATED.webm .
- Powell 2010-09-26 attributed text preserved in https://thunderbolts.info/wp/forum/phpBB3/viewtopic.php?start=90&t=493 : secondary repost, not independently authenticated original.
- Priority: ABHA public before 2013 verified; mathematical Hopfion product and toroidal solitons precede those ABHA sources. Specific claimant pre-2003 formalization and influence on the physicists not evidenced. Preserve each owner's distinct contribution; do not promote a resemblance to plagiarism or a physical prediction.

## Native geometry, BIDI and exact local acceptance
Reuse existing owners, not a replacement 369 model:
- DASHI/Foundations/C3NineSiteAlternatingOrbitExact.agda and C3NineSiteBalancedChartExact.agda
- docs/c3-nine-site-borromean-hopf-maxcut.md, docs/c3-braid-b3-modular-monster-ads3-gravity-maxcut.md
- docs/c3-braid-framing-mobius-endpoint-maxcut.md, DASHI/Mathematics/Topology/HopfU1TransitionCocycleExact.agda
- DASHI/Codec/IndexedCubeMaskSignInstanceExact.agda and DASHI/Core/GovernedIndexedResidualCubeExact.agda, PR #1291
- Docs/papers/drafts/Paper8Section5Draft.md downstream; docs/research/psychotronics-phase1-rodin-study-genealogy-20261025.md separate EM evidence.

The finite phase character on C3 x C3 is (a,b) -> omega^(Pa+Qb). Kernel order 9 if both multiples of 3, otherwise 3. This is a phase-ansatz statement not full spatial symmetry. Preserve P=3kP+rP and Q=3kQ+rQ (signed balanced residues) and C=9kPkQ+3(kPrQ+kQrP)+rPrQ. Local SymPy exact checks executed: 625 signed pairs [-12,12]^2, reconstruction/product/kernel sizes PASS. A=[[1,1],[0,1]], B=[[1,0],[-1,1]]; (AB)^2=[[-1,1],[-1,0]], order 3; (AB)^3=-I; (A^-1 B)^3=[[13,-8],[-8,5]], trace 18. Selected braid presentation discriminator only, not knot invariant under arbitrary Markov moves. Rodin gcd(12,5)=1; an IDEAL closed constant-slope curve would be T(12,5), up to ordered convention and orientation. Actual wire centreline/gluing must be verified; do not assign physical Hopf charge 60 to a coil.

## Roadmap, source-first
H01: exact original FS field ansatz and separate AFZ field/energy; reproduce C=PQ with boundary and orientation conventions.
H02: finite C3xC3 stabilizer proof and source Rodin modulo-nine chart; distinguish cyclic C9 from C3xC3. Reopen full signed carry and seam history.
H03: BIDI winding codec, retaining zero, sign, integer framing, both ordered slopes. Include zero-mode and mirror controls.
H04: compare torus knots, links, Borromean braid; gcd components, ordered slopes, pairwise linking, triple Milnor, framed monodromy; keep Markov distinction.
H05: instantiate actual six H05 transport faces with h,t,k,j,v and retained residuals, not mere equal counts.
H06: reconstruct actual Rodin/ABHA seam and centreline, determine winding, orientation and closure; compare original field preimage with a specified map and no conflation of wire and Hopfion.
H07: numerical energy/stability for original KN model, including (3,2)/(2,3)/(2,2), compare AFZ and standard FS separately.
H08: physical attachment only if same-object gauge representation, dynamics, fermionic quantization and independently measured observables. Bilson-Thompson and Finkelstein/Cadavid are external candidate donors, not QCD confirmation.
H09: retired by user direction; historical source ledger retained, no further personal priority investigation.

Classical authors keep mathematical priority; Rodin/Volk/Powell/Gries keep distinct source credit; project user owns original alternating path; JMD only actual documented contributions; DASHI only existing and new formalization. No new Agda kernel receipt, no CI, no experiment, no claim of priority transfer.


## 25 November — controlling phase/deliverable revision (user direction)

Scope: source archaeology complete for current work; no additional personal priority research. Continue existing #1554 only as the source-specific geometry lane. #1291 remains canonical H05 hyperfabric owner, #1217 physical consumer, #1235 original Hopf bundle owner (closed PR; source reuse, not a claim of kernel acceptance). Paper 8 is a conditional downstream consumer. Do not duplicate source owners or change unrelated PRs. Here H05 denotes the Hopfion roadmap weld invoking canonical H05, not completion of the whole #1291 programme.

### P0A — exact source topology, signed carry and BIDI (H01–H04)
- D1: reproduce the actual AFZ 1999 field and energy and KN 2013 field, potential and boundary conventions independently. Establish map S3 -> S3 -> S2, explicit degree/Hopf composition identity, both signed windings, regular-value fibre/linking and orientation convention. A normalized monomial S3 map is an auxiliary degree witness, not an exact AFZ or KN solution; prove source correspondence. Zero-charge field controls and mirror controls required.
- D2: reuse Base369CirclePhase, Base369TriadicPhaseTower, Base369BinaryTernaryRefinement, Base369PolyphaseCharacters, BalancedTritBitFibre, TriadicFiniteArithmetic. Separate C9 cyclic phases, C3 x C3 angular translations, the signed spatial T27, the order-six spin lift, and the abstract typed eight-vertex cube. For balanced residues r,s define u=bal(r+s).remainder and c(r,s)=(r+s-u)/3. In Z/9 the two-digit chart has law (k,r)+(l,s)=(k+l+c(r,s) mod 3,u); do not delete the carry. The extension C3 -> C9 -> C3 is nonsplit (order-nine element versus exponent-three product). Check the associativity cocycle c(r,s)+c(u,t)=c(s,t)+c(r,bal(s+t).remainder). Exact finite character kernel size 9 or 3; the physical field symmetry is independently gated.
- D3: source-typed record retains ordered (P,Q), coarse quotients and signed trits, phase, integer frame winding, seam and source history. Hopf charge alone is insufficient: (3,2)/(6,1) equal 6 but trefoil/unknot differ; (3,2)/(2,3) same abstract knot but distinct ordered physical parameters; (P,0) collapses charge while P survives. Reuse ConsumerDescentMinimalObserverExact, ConsumerFibreRepairExact and C3BraidFramingInformationLossExact. Deliver roundtrip, factor-through iff constant on fibres, explicit counterexamples, minimal repair for each named consumer, not universal minimality.
- D4: actual curve/link reconstruction using source parametrization; gcd components, oriented linking, trefoil/unknot discriminator, Borromean triple Milnor and integer ribbon framing. Existing selected B3 matrix representation is not a complete Markov invariant; keep source braids and isotopy separately. Formalize the finite/arithmetic portions against existing owners and preserve imported mathematical attribution.

### P0B — continuous geometry and indexed transport (H05–H06)
- D5: recover actual Rodin/Volk Fig 2 / Table 9 seam, directed path, closure permutation, lifted integer winding and reverse traversal. Ideal (12,5) curve is only a comparator until source centreline is reconstructed. Use actual source coordinates; compare ABHA electrical activation separately from conductor geometry. Reuse C3NineSiteBalancedChartExact and C3NineSiteAlternatingOrbitExact; retain geometric embedding, normal framing and sample/time history. Prove a clearance-based conditional isotopy/sampling lemma before arbitrary refinement promotion.
- D6: use GovernedIndexedResidualCubeExact, canonical blob 42b70ebb7376813076934f2245ce6011b76f10c8, IndexedCubeMaskSignInstanceExact, ConsumerIndexedResidualRefinementExact. Candidate axes: X reversible source encoding/refinement, Y actual winding/phase or braid operator evaluation, Z nonidentity frame/phase action with conjugation/covariance. Build eight typed vertices, twelve actual maps, six face witnesses and six endpoint path receipts. On noncommuting faces retain actual signed/order-sensitive residual; no false ExactFaces receipt. Separate h,t,k,j,v, source identity, physical spatial cube and consumer. Latest #1291 Y443 retained-residual operator and SSP history lanes are architectural donors only, not source-specific Hopfion evidence. Accept only when inverse recovery, zero/nonzero/mirror controls and source-specific covariance pass. Smooth Hopf atlas, overlap cocycle, Chern class and framed lift reuse #1235; no implicit smoothness claim from finite charts.

### P1 — original model dynamics (H07)
- D7: independent AFZ exact reference versus original KN energy/EL equations; reproduce source parameters, finite-energy boundary, topology-preserving relaxation, (3,2)/(2,3)/(2,2) and equal-charge unknot controls. Measure energy terms, stationarity residual, mesh convergence, Hopf invariant preservation, Hessian/perturbation spectrum and seed sensitivity. Failure to find a solution is not a nonexistence proof. GPU-native numerical path where supported; exact local SymPy for symbolic checks; no CI. Preserve checkpoints for long jobs. Rodin electromagnetic model uses actual current/geometry and Maxwell evidence as a separate producer, not the KN action.

### P2 — downstream physical attachment (H08)
- D8: compare Finkelstein/Cadavid quantum-group and Bilson-Thompson framed-preon representations against Paper 8's actual charge/chirality and colour/weak/hypercharge consumers. Reuse KKBraidMoonshineGaugeSameObjectCutExact, KKHopfSpinExistingOwnerWeldExact and actual gauge owners. Explicit intertwiner, configuration-space Finkelstein–Rubinstein quantization, gauge action, anomaly/charge checks and independently testable observables or exact obstruction. No identification of quarks from visual topology, no claim of new fundamental particles, no physical TOE promotion. P2 does not block P0 mathematical work.

### Fresh exact local audit in this turn
Executed Python/SymPy independently: 625 ordered signed pairs P,Q in [-12,12] (roundtrip, C expansion, 9/3 stabilizer); all 27 balanced residue triples (carry cocycle); all 81 C9 addition pairs (two-digit chart with carry); selected B3 matrices (central sign, order and Borromean monodromy) PASS. These are finite or symbolic algebra checks, not an Agda receipt or continuum proof. The general carry identity follows by telescoping the integer section equation; formal source attachment remains open. Reproduction: balanced(n)=( (n-r)//3, r ), r=(n+1)%3-1; enumerate product ranges and test identities above. No CI.

### Attribution invariant
Classical Hopf, torus-knot, braid, extension/cocycle and spin mathematics stays with its established authors/tradition. AFZ own their exact integrable solitons; Faddeev/Niemi/Battye/Sutcliffe their respective field/numerical work; KN their original domain-wall and kink models; Rodin/Volk their documented map/coil; Powell/Gries their distinct ABHA presentations; Finkelstein/Cadavid and Bilson-Thompson their candidate particle constructions. The project user owns the documented alternating nine-site path. JMD owns only documented JMD inputs (e.g. actual donor geometry/SSP work), not unrelated external results or every 369 extension. DASHI owns its pre-existing signed/residual/transport machinery and genuinely new implementation, comparison, counterexamples and proofs; retain original module/PR provenance and distinguish source-written, local execution, kernel acceptance, physical evidence. No attribution by analogy or reassignment of priority.


## 25 November 2026 — P0A continuous reference and original YM369/NS369/atomic donor contraction

Controlling scope: continue #1554, retain D1–D8 above and the original owner boundaries. No competing PR, no edit to YM/NS/Paper 8 owners, no CI invocation. Use native GPU for numerical evolution when actually available; exact local SymPy for symbolic work. This is an actual smooth classical degree-one reference, NOT the original AFZ/KN stationary solution and NOT a physical particle claim.

### P0A.1 — executed normalized Hopf/Whitehead source (partial D1)

New executable `scripts/check_hopf369_source.py`, commit 7d6c29e92c3af6c5a1eb680a1954f832f5992789, blob 3aaa7a11a31a716fb9c7626fb318161ccdb0a2f0. Local SymPy 1.14.0: 22/22 exact checks PASS; committed Git blob matches the locally executed bytes. Reproduce with `python scripts/check_hopf369_source.py`. Classical Hopf map and Whitehead integral are established prior art; DASHI contribution is exact source-specific cross-consumer construction and discrimination.

Set D=1+x²+y²+z², q=(a,b,c,d)=(2x,2y,2z,D−2)/D. This inverse stereographic map extends to S³, q(infinity)=(0,0,0,1). The Hopf map n=(2(ac+bd),2(bc−ad),a²+b²−c²−d²) satisfies |q|²=|n|²=1. For A=a db−b da+c dd−d dc, using the Euclidean metric in the stereographic chart,

A=2/D² (2xz−2y,2x+2yz,1−x²−y²+z²), B=curl A=4A/D.

For the outward unit-sphere area form ω (integral 4π), n*ω=−2 dA (all three coefficients checked). Thus Ω=ω/(4π) has primitive −A/(2π). Q=∫A∧dA/(4π²)=1 because A·B=16/D³; mirror pullback reverses Q to −1. |A|²=4/D², |B|²=64/D⁴, div B=0. Algebraic identities and radial integral executed; smooth compactification follows from the stereographic construction, but no machine-checked atlas, regular-value linking computation or AFZ/KN equation residual is claimed. In particular Q alone cannot recover the ordered windings/framing. D1 zero-charge field and signed (P,Q) source comparisons remain active.

### P0A.2 — actual NS/MHD/EM initial-field and reverse controls

Reuse #443 `NavierStokesHopfNoetherContinuationGateExact`, #1164 `OrientedThreeAxisBracket369Exact`, `NSCross369OrientationBridgeExact`, #1271/#1279 R734/R735 and #1551 R568 signed rate-resolved same-source cut; MHD `MHDMagneticHelicityThreeLegBidiExact` and its original inverse-curl owner. Read-only donors, not evidence of physical equivalence.

* A is not Euclidean Coulomb gauge or incompressible velocity: div A=4z/D². B is smooth, divergence-free, finite-energy, and can be selected as Euclidean R³ initial velocity u=B (separate from the magnetic interpretation). Kinetic energy ∫|B|²/2=4π²; kinetic helicity ∫B·curl B=20π² (density 256/D⁵), whereas magnetic helicity ∫A·B=4π². No identification of kinetic helicity with integer Hopf charge.
* Actual non-gradient nonlinear term: curl(B×curl B)(1,0,0)=(-4,0,0). Hence B is not a stationary unforced Euler field on Euclidean R³ and the Leray projection of its Lamb vector is nonzero. Pointwise parallelism B=4A/D is NOT a constant-curl eigenfield theorem, and is not stationarity or stability.
* Reverse target: recover a gauge-fixed potential from the solenoidal field with stated decay/zero-mode and harmonic-sector boundary conditions; preserve gauge fibre, orientation, amplitude and phase, not just helicity. Prove same-source Gauss linking/regular-value interpretation, then fill actual HopfHelicityBridge fields rather than declare the record inhabited. For NS distinguish R³ from original periodic Galerkin torus; provide a source-specific periodization/cutoff comparison with divergence, reality, helicity, time/scale, error and energy receipts before using R568/R734. MHD: construct actual initial induction state, consume inverse-curl and ordered three-leg variation, pay the open reality-paired cancellation where applicable; dynamical ideal/resistive and boundary-flux laws separately. No NS regularity or MHD conservation proof from topology alone.

### P0A.3 — exact non-Abelian projection, not connection identity

Reuse #1531 `YM369KKHopfC3DonorWeldExact`, `SU2Bracket369OrientationBridgeExact`, `BalabanCMP109SpatialC3ActionExact`, `HopfQuaternionAxisProjectionExact`, `HopfU1CosetOrbitExact`, `U1SU2GroupTorusExact`, and #1235 smooth bundle obligations. For imaginary-quaternion basis with bracket 2 cross, right Maurer–Cartan R=dq q^-1 satisfies dR−R∧R=0 (three components checked as vector equations for each coordinate pair); the connection −R is flat. A is the first imaginary component of R. The projected Abelian curvature dA is nonzero (B(0)=(0,0,8)). Thus projection can yield nonzero curvature from a flat full connection: the omitted transverse commutator supplies it. This is an explicit reduction discriminator, not a gauge equivalence or a physical Yang–Mills Hopfion. Retain #1531 BPST/Cartan commutator obstruction, and #1536 literal Wilson 1024 links/1536 plaquettes and weighted observables as source-transport standard; no promotion to CMP119/102 or Clay.

### Controlling remaining deliverables (P0 before P1/P2)

| Gate | State / next exact payment |
|---|---|
| D1 continuous topology | PARTIAL: executed degree-one reference/mirror. Actual source AFZ/KN maps, degree/linking conventions, zero and signed P,Q controls, source atlas and boundary still due. |
| D2–D4 finite carry and braid | Prior finite receipts retained; source-typed formal roundtrip and actual regular-value/framed links remain. |
| D5–D6 indexed source | OPEN: actual Rodin/Volk and ABHA seam/history; reuse #1291 H05, eight typed vertices/twelve maps/six faces/six paths with signed residual and index independence. Evaluate actual operators, including noncommuting phase, not fixed adjacency or scalar winding alone. |
| D7 dynamics | OPEN: original AFZ/KN action/Euler–Lagrange reproduction, residuals, topology-preserving convergence and Hessian/stability; independent Maxwell/MHD/NS source evolution. |
| D8 particle quantization | OPEN: original configuration-space FR loops, gauge action, charge/chirality, representation and independent observables. |
| D9 qutrit algebra | REUSE `DASHI.Algebra.Quantum.QutritWeyl`, original X³/Z³ and ZX=ωXZ, plus Monster finite Heisenberg owners. Derive explicit indexed central cocycle and octet action/adjoint, do not create another Weyl owner. |
| D10–D11 quantum/atomic | Reuse #886/#1141/#1194/#1217: compare atomic s+p spin representation vs traceless Weyl operator adjoint sector, actual signed intertwiner or obstruction; exterior/Hodge and spin lift are not particle identity. |
| D12–D13 atomic continuum | Existing same-object kinetic covariance and continuum-to-interacting-Hamiltonian projection frontier, exact selected 2p² Coulomb fixture remains scoped. |
| D14–D16 consumers | Operator six-face indexed transport; atomic kernel6/Monster coordinate bridge with actual action assignment; spectroscopic observable residual and validation. |
| NS/MHD attachment | PARTIAL initial field and nonstationarity above; construct gauge/metric/boundary and physical inverse witnesses; real dynamics/time-integrated controls open. |
| YM attachment | PARTIAL exact Cartan projection; smooth transition/connection and genuinely non-Abelian action/curvature/soliton source remain open. |

Keep source identity, physical time, refinement, chart, orientation, signed residual, zero, phase, winding, frame and consumer independently typed. Do not mark generic constructors or reference fields as paying original source equations. Next large bite: explicit signed (P,Q) normalized smooth family and original AFZ/KN variational residuals, with original source conventions and separate physical helicity/connection realizations; do not wait for generic infrastructure.

Attribution: classical Hopf/Whitehead, Maurer–Cartan, Moffatt/Arnold–Khesin helicity and Navier–Stokes/Waleffe, Yang–Mills/Wilson, Weyl and existing original AFZ/KN and atom-physics authors retain credit. User-directed geometric BIDI/reverse-solve and DASHI new exact computations explicitly distinguished; JMD only documented donor contributions. No new kernel receipt, original donor rerun, physical experiment, or solved Clay/TOE claim.
