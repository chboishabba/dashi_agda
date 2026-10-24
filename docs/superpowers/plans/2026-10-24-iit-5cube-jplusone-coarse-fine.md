# IIT \(5^3\) diagonal lost modes ↔ J+1 / JCoarse / JFine — exact max-cut

**2026-10-24 · Source owner:** [dashi_agda #1148](https://github.com/chboishabba/dashi_agda/pull/1148), *open/unmerged*. **Cross-lane roadmap:** [#1246](https://github.com/chboishabba/dashi_agda/pull/1246). **Scope:** one finite, linear \(\mathbb F_3\) 5×5×5 periodic operator; no IIT-Φ, physiological, vacuum, magneto-optical, phenomenal, or literal modular-\(j\) identification.

## 0. Attribution and actual same-object roots

**Pre-existing DASHI algebra:** \`scripts/iit_ternary_lattice_scaling.py\` computes rank over \(\mathbb F_3\) of the cyclic \(x+y+z\) operator \(F\) on the 125-site 5×5×5 carrier; its rank is 120 and nullity 5. \`scripts/iit_lattice_scaling_experiment.py\` is a separate existing scaling/geometry check. \`IITCubeConcreteTorusImageExact.bop3Neg\` owns the different *3×3 ternary face* theorem \(B^3=-I\); do not confuse that operator with the 5³ operator. \`IITLatticePrimePowerSourceBridgeExact\` documents the char-\(p\) periodic power result for \(n=p^k\). **This 5-side example is not a \(p^k\) side length** for \(p=3\), so the Frobenius identity \(F^{p^k}=dI\) cannot directly prove its 80-step decomposition.

**Older DASHI J sources, already present before this work:**
- \`DASHI/Foundations/JPlusOneScaleBridge.agda\`: \`FreshUnitExtension\` for literal stage \(10+1=11\) and separately \(196883+1=196884\). Same addition *shape*, different authorial/theory roles; neither is a new spatial axis.
- \`DASHI/Biology/JFineCoarseRelativeScaleExact.agda\`: \(j_{\rm coarse}=9\), \(j_{\rm relative\ fine}=3^9=19683\), absolute product \(3^{11}=177147\), with coarse depth 2 plus relative fine depth 9.
- \`DASHI/Biology/JCoarseFineEvaluationFibreExact.agda\`: pointed evaluation at the distinguished completion channel; a fine codomain of size 19683 does **not** assert every fixed-value fibre has 19683 assignments.
- \`DASHI/Core/CoarseFineRelativeFibreExact.agda\` and \`DASHI/Biology/JCoarseFineConsumerReductionBridgeExact.agda\`: exact \((\mathrm{coarse},\mathrm{relative\ fine})\) reopening and consumer-factorisation / non-descent.
- \`DASHI/Core/RelationalCoordinatePlusOneCrossPollinationExact.agda\`, \`JCompletionTrivialLineSeparationExact.agda\` and \`Base369JCoarseFineStableIdentityDisciplineExact.agda\` explicitly warn that distinct unit roles, carriers and cardinality coincidences cannot be identified.

**New DASHI derived result:** \`scripts/iit_j_coarse_fine_5cube_audit.py\` verifies the **concrete full operator identity below on every one of 125 basis vectors**; \`DASHI/Biology/IITFiveCubeJCoarseFineRelativeBridgeExact.agda\` consumes the earlier generic coarse/fine theorem to derive a *conditional exact reopening* from a supplied algebraic projector identity. It deliberately does not claim an Agda inhabitant of the concrete 125-state operator or a kernel-checked generic 5³ spectral theorem. Source-written proof and finite numeric/algorithmic authority remain separate.

**External mathematical context, not source of a new consciousness claim:** rank–nullity, group-algebra cyclic shifts and linear projections are standard finite-field linear algebra. The Scott Aaronson/Giulio Tononi 2014 large-grid IIT debate and Albantakis et al. 2023 IIT 4.0 concern different IIT and physical interpretation layers; the repository authorship attaches only to our finite operator and consumer synthesis.

## 1. The five dimensions really are one diagonal cyclic profile

Let \(V=\mathbb F_3^{(\mathbb Z/5)^3}\), dimension \(5^3=125\), and \(W=\mathbb F_3^{\mathbb Z/5}\), dimension \(5=5^1\). With all indices periodic, define:

\[
(Fx)_{i,j,k}=x_{i+1,j,k}+x_{i,j+1,k}+x_{i,j,k+1}\pmod3.
\]

**Embedding of the lost diagonal modes** \(J:W\to V\):

\[
(Jg)_{i,j,k}=g(i+j+k\bmod5).
\]

Each coordinate value \(s=i+j+k\) labels one 25-site diagonal plane; \(W\) specifies **one five-slot profile** with values \(g(0),...,g(4)\). Because changing any of \(i,j,k\) by one increments \(s\) by one,

\[
F(Jg)=3g(s+1)=0.
\]

Define the extraction \(P:V\to W\) by **summing** each diagonal plane,

\[
(Px)(s)=\sum_{i+j+k=s\pmod5}x_{i,j,k}\pmod3.
\]

Because every plane contains 25 sites, \(25\equiv1\pmod3\):

\[
PJ=\mathrm{id}_W,\qquad PF=0,\qquad FJ=0.
\]

Hence \(J\) is a *canonical injective 5-dimensional null-channel*, not 5 mysterious additional spatial sites or a fourth spatial direction.

## 2. Stronger than rank: complete fine/core decomposition

The new finite audit checks the exact operator equation

\[
\boxed{F^{80}=I_V-JP}
\]

on all 125 standard basis vectors. All maps are linear over \(\mathbb F_3\), so basis verification establishes it for every state. This is a finite exact arithmetic certificate—not a statistical fit or an Agda kernel compilation.

Consequences follow *without* assuming that rank 120 alone proves long-time behaviour:

1. \(\ker F = \mathrm{im}J\). The inclusion \(\mathrm{im}J\subseteq\ker F\) follows from \(FJ=0\). If \(Fx=0\), \(F^{80}x=0\), so \((I-JP)x=0\) and \(x=JPx\).
2. \(\mathrm{im}F=\ker P\). One inclusion follows \(PF=0\). If \(Px=0\), \(x=F^{80}x=F(F^{79}x)\), so \(x\in\mathrm{im}F\).
3. \(V=\underbrace{\mathrm{im}F}_{120\ \mathrm{dimensions}}\oplus\underbrace{\mathrm{im}J}_{5\ \mathrm{dimensions}}\) because \(PJ=\mathrm{id}\). The two canonical idempotent projectors are \(I-JP=F^{80}\) and \(JP\).
4. \(F\) is **invertible on the 120-dimensional retained core** \(\mathrm{im}F\) with \(F^{80}=\mathrm{id}\) there. The modes lost on the first step are exactly the 5-dimensional diagonal-profile subspace; no new core dimension is lost at later steps.
5. The actual **source can be reopened from the observed update plus the five-slot residual**:

\[
\boxed{x=F^{79}(Fx)+J(Px).}
\]

This is precisely the kind of *consumer-relative exact residual reopening* encoded by the existing JCoarse/JFine and \`CoarseFineRelativeFibreExact\` owners.

The number of source states is \(3^{125}\). The update's image has \(3^{120}\) possible states and each observable has \(3^5=243\) preimages. This is a **multiplicative factorisation of configuration counts**, not spatial cardinality \(125+5=130\).

## 3. What "+1" does and does not mean

The strongest defensible interpretation of the user's proposed “5³ plus lost five = +1” is:

> At fixed 5×5×5 spatial geometry, five missing state coordinates form **one additional cyclic profile packet** indexed by \(\mathbb Z/5\), with five trits of independent residual data. Relative to the 120-dimensional observed/core state, \(120+(1\times5)=125\).

It does **not** mean \(125+5=130\) independent dimensions in the original state, nor \(5^4=625\) spatial sites, nor a new *one-scalar* \(\mathbb F_3\) dimension. The two spaces \(W\) (five trits) and \(V\) (125 trits) have different indexing; a relative fibre can have five coordinates without being a physical extra axis.

The existing \`JPlusOneScaleBridge.FreshUnitExtension\` provides an **arithmetic shape adapter** for this one packet (\`carrierValue=120, freshValue=5, joinedValue=125\`), not an identification with the original stage-11 or McKay fresh unit. Likewise the *original* harmonic \(j_{\rm coarse}=9\), \(j_{\rm fine}=19683\) are **not** suddenly \(5\) and \(3^5\). They are distinct typed carriers.

This is much closer to the repo's **consumer-sensitive fibre restoration** than to a speculative higher-dimensional torus.

## 4. Adversarial controls: the '+one profile' is not universal

Existing source scans over the SAME three-axis ternary rule:

| Side length | Sites | Rank | Kernel dimension |
|---|---:|---:|---:|
| 3 | 27 | 18 | 9 |
| 4 | 64 | 60 | 4 |
| 5 | 125 | 120 | 5 |

The 3³ lattice has *nine* lost trits, not three; \(3\mid n\) introduces additional nonsemisimple degeneracy. The 4³ and 5³ examples each have a one-\(n\)-slot kernel **in these exact source cases**, but that does not establish \(\dim\ker F=n\) at every \(n\). In fact, at \(n=8\) the 8th roots of unity live in \(\mathbb F_9^\times\), and there are \(8\cdot7=56\) ordered nonzero triples summing to zero in characteristic three. This predicts a 56-dimensional kernel for the periodic ternary three-axis 8³ map, whereas a universal one-profile rule would predict only 8. This is an analytic algebraic counterexample, not a rank-matrix replay of 512 sites, and lies outside the source script's original n≤5 3D scan.

Controls for promotion: change periodic/open boundaries, algebra F₂/F₃, n, number of active axes, local law (e.g. majority instead of affine sum), and state-dependent nonlinearity. Without source-preserved correspondence, neither neural memory nor the historical hypothetical conscious grid inherits the present projection.

## 5. Roadmap / acceptance

**D3B.5 — DONE as source/audit:** n=5 diagonal embedding, plane extraction, 125-basis \(F^{80}=I-JP\), full-core/reopening identities, cross-size falsifiers. \`scripts/iit_numeric_verification.py\` now consumes the source-level five-cube audit on the **IIT PR #1148 branch**. Independent local full-basis calculations passed before committing; an exact-head runtime receipt for the newly committed Python script must be recorded separately.

**D3B.6 — OPEN mathematical formalisation:** lift the concrete 5³ \(\mathbb F_3\) operator and \(P,J,F^{80}\) identity into an Agda carrier, **or** a validated finite certificate checker that the Agda kernel consumes. The new \`IITFiveCubeJCoarseFineRelativeBridgeExact.agda\` proves the generic “power certificate ⇒ coarse/fine reopening” theorem conditional on the missing concrete operator receipt. Do not promote the record's Boolean scope labels to theorem authority. Exact-head Agda build pending.

**D3B.7 — CONDITIONAL external consumers:** instantiate a measured connectome/brain/AI hidden trajectory with a genuinely 5-trit consumer-relevant residual and show same-object projection/transition. A diagrammatic \(5^3\) coincidence, 5-dimensional numerical nullspace or analogy to J+1/Monster does not satisfy this. IIT system \(\varphi_s\), full CES/Phi, phenomenal identity and quantum signatures remain source-specific independent gates.

**Acceptance commands (not automatically run by this document):**
\`\`\`sh
python3 scripts/iit_j_coarse_fine_5cube_audit.py
python3 scripts/iit_numeric_verification.py
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/EverythingIITPhiIntegrationMaxCut.agda
\`\`\`
Record exact SHA, Python/Agda versions, output hashes, and whether the run consumed the same original source matrix. J coarse/fine is a **reuse contract**, not numerical or physical identity.


### Two consumer-relative coarse/fine orderings (additional max-cut)

The Agda bridge now exports **both** structurally exact reopening contracts from the same conditional \(F^{80}=I-JP\) producer:

1. **Geometric coarse first:** coarse \(P(x)\) (five-slot diagonal profile), relative fine \(F(x)\) (120-dimensional retained dynamics), reopening \((g,y)\mapsto F^{79}y+Jg\). This closely matches the intended *coarse point with relative fine assignment* interpretation, but is not the old J harmonic carrier.
2. **Dynamics-observation coarse first:** coarse \(F(x)\) (the actually seen one-step output), relative fine \(P(x)\) (five missing trits), with the same reopening equation. This is the direct consumer-relative non-descent view: two source states differing by a kernel profile have the same update output but differ for a \(P\)-sensitive consumer.

Neither orientation automatically becomes the sole correct ontology. Both require the **same concrete 5³ operator certificate**; changing observation \(Q\) or target \(T\) changes which residual qualifies as necessary. In either ordering, no independent state dimensions are added to the original 125.


### The geometrically strongest "+1": a constrained fourth *address* coordinate

One can make the analogy literal **at the level of index charts** without adding independent physical/state dimensions. Define:

\[
\Gamma_s=\{(i,j,k,s)\in(\mathbb Z/5)^4:\ s=i+j+k\bmod5\}.
\]

The graph map \( (i,j,k)\mapsto(i,j,k,i+j+k)\) is injective, with inverse the projection to the first three coordinates. Thus \(|\Gamma_s|=5^3=125\), whereas the unconstrained ambient fourth-coordinate address space has \(5^4=625\) points. The fourth *address label* is dependent, not a fourth independent spatial axis. Its five possible values label the five disjoint 25-site diagonal planes, and the missing modes are precisely the **functions \(g(s)\)** on that label.

This is the strongest defensible geometric formulation of “\(5^3\) + one” here: **three free cyclic address coordinates plus one dependent chart coordinate**, carrying a five-trit consumer residual. Neither cardinality \(125+5\) nor physical dimension \(4\) follows. The Python audit now checks graph injectivity and the 125-vs-625 distinction alongside \(F^{80}=I-JP\).


## Concrete typed identification of harmonic/pointed/punctured carriers — 2026-10-24

**New authoritative source/audit:** [selected/punctured 79/80/72 JFine proof roadmap](./2026-10-24-iit-jfine-79-80-72-selected-pointed.md).

The earlier warning that these carriers had *not been identified* is now partially discharged: the **literal underlying source carriers** have an explicit two-sided codec. The pre-existing J fine nine-trit phase table splits into five D4-set-stable cross positions C,N,E,S,W and four corner trits, giving \(3^9=3^5 3^4=243\cdot81=19683\), with roundtrips into the *actual* Fin19683 source. The nine ordinary coarse channels plus the distinguished completion channel map two-sided to the *actual* nine marked or one unmarked pointed sheet. The sheet's independently named trit constructors are also converted explicitly. Thus the old elementary harmonic and the old pointed sheet with 196830 states are actually registered as **finite data carriers**.

Four corner trits equipped with an explicit chosen quartic multiplication make F81, whose nonzero group has 80 states, and 79 is its inversion exponent. Original punctured four-trit source proved the cardinal 80 but not this multiplication. Fifth-root eigenvalue orders in the actual 5-cube: zero(5), 8(12), 16(12), 40(48), 80(48). The F80 period of retained dynamics is **sharp** (48 primitive-order-80 eigenvalues), not just a bound. Nine-element subfield has affine group of order 9*8=72; source p2 punctured eight states are not automatically that same group action.

**Obstruction remains:** the 5-cube kernel's C5 translation cannot embed into the original phase-translation C3² or square D4 actions (their orders 9 and 8). The selected five coordinates are D4-stable *as a set*, not under the same C5 cyclic order. A chart choice provides an ordinary bijection/embedding, not that missing natural equivariance. No Monster module, actual j-invariant field identification, quantum mechanism, or phenomenal/physical theorem is claimed. Exact-head Agda and newly committed script execution receipts remain open.
