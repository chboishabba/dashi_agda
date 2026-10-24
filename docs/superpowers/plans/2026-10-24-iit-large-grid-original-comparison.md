# Original-conscious-grid comparison and large-grid periodic XOR audit

**Date:** 2026-10-24 (Australia/Brisbane). **Owner:** dashi_agda IIT/phi PR #1148. **Scope:** correct the mistaken extrapolation of the repo's 2×2 nilpotence to larger lattices. This note is an exact finite-linear-algebra / provenance max-cut, not a full IIT structure computation or evidence of consciousness.

## 1. Original source roots and attribution

1. **Scott Aaronson** (2014), ["Why I Am Not An Integrated Information Theorist (or, The Unconscious Expander)"](https://scottaaronson.blog/?m=201405) and follow-up discussion. An adversarial critique, with expander networks and very simple XOR computations, of earlier IIT's implied consciousness classifications. Original author owns this criticism, not the DASHI finite model.
2. **Giulio Tononi** (2014), ["Why Scott should stare at a blank wall and reconsider (or, the conscious grid)"](https://learniit.org/corpus/tononi-2014a). The original response explicitly considers an illustrative **1,000×1,000 physically realised** 2D lattice with appropriate connections and **e.g. majority-input gates**, even with all sites off. This is a theoretical example, **not a measured one-million-node dataset or full million-node PyPhi calculation**. Do not replace this physical local law by the DASHI east-plus-south XOR map without stating it is a controlled *alternative*.
3. **Larissa Albantakis et al.** (2023), IIT 4.0, DOI 10.1371/journal.pcbi.1011465. Primary theoretical source for the 2023 system intrinsic-integrated-information definition. **PyPhi** [version guide](https://pyphi.readthedocs.io/en/latest/howto/earlier-versions.html) explicitly separates IIT 3.0, IIT 4.0 2023 and IIT 4.0 2026. In particular 2026 imposes an intrinsic-information requirement on system φₛ; a difference in version is not a physical change in the grid.
4. **DASHI 2026** owns: \`IITXORGridAdversarialExact\` 2×2 toy; \`IITXORGridTwoStepDynamicsExact\` finite F²=0 witness; \`IITCubeConcreteTorusImageExact.bop3Neg\` 3×3 ternary face B³=−I; \`IITTernaryLatticeStateSpaceScalingExact\` counting boundary; \`scripts/iit_lattice_scaling_experiment.py\` and \`scripts/iit_ternary_lattice_scaling.py\` original larger-grid ranks and slab diagnostics; NEW \`IITLatticePrimePowerSourceBridgeExact\` source-reused finite comparison and \`scripts/iit_lattice_prime_power_audit.py\` independent scan/check.
5. Other sources or later discussions are not counted as independent witnesses to the 2014 debate. A developer-written causal map, a literature theory, an empirical physical network, a Python rank calculation and an Agda kernel receipt have different owners and authority.

## 2. What our prior large-grid work actually computes

**Already existing on #1148:** \`iit_lattice_scaling_experiment.py\` enumerates **2D periodic side lengths n=2..10** over F₂ and F₃ and a 3×3×3 ternary cube. \`iit_ternary_lattice_scaling.py\` covers **2D n=2..10**, **3D n=2..5** over both alphabets and a 3×3×3 stacked-face control. Hence the declared range reaches **10×10=100 spatial sites** and **5³=125 sites**. These are generated matrices, not necessarily the same physical grid as Tononi's hypothetical example. The scripts return matrix rank, nullity, reachable configurations, predecessor counts and an algebraically declared slab cut with stated cause-selectivity.

**What was NOT done by those scripts:** exhaustive enumeration of all binary configurations of a 100-site system (2¹⁰⁰), full PyPhi/CES/big-Phi on the 100- or 125-site systems, a physical recording, or the original million-site hypothetical grid. In the code, the label \`zero_state_declared_cut_phi_s_bits\` describes a **particular separately constructed cut proxy**; **it is not the minimum partition of the original IIT system analysis**. Use the explanatory label \`declared_slab_proxy_bits\` in publications, even when preserving the legacy JSON key for compatibility.

## 3. Exact algebraic theorem for the source-periodic model

Let \(G=(\mathbb Z/n\mathbb Z)^d\), \(V=\mathbb F_p^G\), and let the commuting shifts \(S_i\) act by cyclically translating the i-th coordinate. Define

\[
F = \sum_{i=1}^{d}S_i,\qquad (Fx)(c)=\sum_{i=1}^d x(c+e_i)\pmod p.
\]

If \(n=p^k\) then each \(S_i^{p^k}=I\), and the characteristic-p Frobenius (Freshman's dream) identity for commuting endomorphisms gives

\[
\boxed{F^{p^k} = \sum_{i=1}^{d}S_i^{p^k} = d I \quad\text{over }\mathbb F_p.}
\]

This proof is fully mathematical under the stated toroidal/finite-field hypotheses; **a general arbitrary-side-length Agda kernel theorem has not been constructed here**. It DOES NOT apply to arbitrary boundary conditions, majority gates, threshold neurons or historical IIT causation scores.

Consequences:
- F₂, 2D, n=2^k: \`F^n=0\`. The **2×2 toy is one instance**, not a general claim about all square grids.
- F₂, 3D, n=2^k: \`F^n=I\`. Dynamics are invertible/periodic despite the same XOR local syntax. Explicit checked n=2,4.
- F₃, 2D, n=3^k: \`F^n=2I=−I\`, so \`F^{2n}=I\`. This reuses the kernel-candidate \`bop3Neg\` on the literal 3×3 face from earlier IIT #1148; six-step identity is now an explicit source-written Agda consequence.
- F₃, 3D, n=3^k: \`F^n=0\`. Explicit checked n=3, 27 sites. It agrees with earlier cube image rank 18 on the actual three-face dynamics, but the equality of formulations requires the same coordinate/step chart; no unconditional kernel import is claimed for this new general statement.

For **every** n on the 2D cyclic torus with local law \`Sx+Sy\`, the exact nullity is:
- p=2: \`dim ker F = n\`, \`rank=n²−n\`;
- p=3: \`dim ker F=n\` if n is even, otherwise \`0\`.

Proof: \`Fx=0\` implies \`x(i+1,j) = −x(i,j+1)\`. Along each of the n residue classes of \`i+j\`, values alternate by a factor \`−1\`. Closure after n steps permits a nonzero degree of freedom per class iff \`(−1)^n=1\` in the field. This includes all n in characteristic 2; in characteristic 3 it occurs exactly for even n. An invertible 2D ternary odd-n map has no state-loss dimension. In particular **n=1000 binary toroidal XOR** would mathematically have rank 999,000 and kernel dimension 1,000, but this is an *analytic extrapolation*, not a 1000×1000 simulation and not the same local law as Tononi's illustrative majority-gate physical grid.

2D F₂ is nilpotent iff n is a power of two, since the invariant subspace of configurations independent of the second coordinate carries the cyclic-shift-plus-identity operator, which is nilpotent only for power-of-two cycle length (the other direction follows from Frobenius). Consequently **n=10** is not globally nilpotent, although its one-step kernel still has dimension 10. Do not write "loses ten *new* dimensions each step"; one-step rank-nullity does not establish timewise loss rate.

## 4. Independent local finite test results (not kernel receipts)

Run \`python3 scripts/iit_lattice_prime_power_audit.py --json <path>\` on the IIT branch. A separate independent source-faithful standard-library Python calculation was executed in this research turn and reported:

| Field | Geometry | Sites | Rank | Nullity | Extra dynamics |
|---|---|---:|---:|---:|---|
| F₂ | 2D 2×2 | 4 | 2 | 2 | F²=0 |
| F₂ | 2D 3×3 | 9 | 6 | 3 | nonzero persistent orbit, F⁴δ=Fδ |
| F₂ | 2D 4×4 | 16 | 12 | 4 | F⁴=0 |
| F₂ | 2D 8×8 | 64 | 56 | 8 | F⁸=0 |
| F₂ | 2D 10×10 | 100 | 90 | 10 | F¹²⁸δ ≠ 0 |
| F₂ | 3D 4³ | 64 | 64 | 0 | F⁴=I |
| F₂ | 3D 5³ | 125 | 125 | 0 | full-rank, no formula inferred for general n |
| F₃ | 2D 3×3 | 9 | 9 | 0 | F³=−I |
| F₃ | 2D 10×10 | 100 | 90 | 10 | noninjective |
| F₃ | 3D 3³ | 27 | 18 | 9 | F³=0 |
| F₃ | 3D 5³ | 125 | 120 | 5 | partial loss |

The separate arithmetic scan checked 26 n/p/d parameter rows and 8 prime-power \`F^n=(d mod p) I\` cases *against all basis vectors*, not just random states. A signed JSON receipt under \`/mnt/data/iit_lattice_prime_power_audit.json\` was created separately. The exact **new GitHub script** was committed but **was not executed from a GitHub checkout in the present connector-only environment**; do not present local independent tests as exact-head script receipts. No Agda toolchain execution or direct PyPhi package replay took place.

## 5. Relation to the original historical grid and IIT

Tononi's thought experiment requires a specifically **physically realised** connected grid of elements with causal power, appropriate gates (he offers majority gates as an example), and a phenomenology-to-causal-structure interpretation. The DASHI periodic east/south XOR transform is **not** that same physical mechanism; changing periodic to open boundaries, local threshold to XOR, or zero to another current state changes the analysis. We cannot use finite rank to refute or validate historical phenomenological claims. Nor can the 2014 IIT 3.0 value be silently identified with IIT 4.0 2023 or 2026 \`phi_s\` or complete cause–effect-structure \`Φ\`.

The exact fact that **different fields/dimensions/side arithmetic give different long-time behaviour** is useful in adversarial testing of naive explanations of:
- neuron functional geometry, memory retention, recurrent activity and excitability;
- learned geometric reasoning / LILA hidden-action dynamics;
- intrinsic geometric/qualia-theory predictions;
- claimed quantum/zero-point/toroidal physical mechanisms.

But physical identities, neuronal state dynamics, quantum signatures, conscious access and phenomenal consciousness remain **separate source-specific gates**. One periodic finite-field algebra never settles them by analogy.

## 6. Revised phases, deliverables, stop conditions

- **D3B.1, source archaeology complete:** original Aaronson/Tononi source versions and the pre-existing n<=10 / n<=5 matrix scripts verified. No need to repeat generic ranks as a new discovery.
- **D3B.2, mathematical closure largely paid:** exact Frobenius identity proof given; reproducible independent finite rank/dynamics test; finite Agda 2D ternary B³/ B⁶ source owner. Outstanding a **generic Agda Frobenius and arbitrary n 2D nullity kernel** if needed by downstream proof, with exact-head receipts.
- **D3B.3, experimental IIT actual-formalism frontier:** distinguish historical IIT 3.0, PyPhi IIT_4_0_2023, and IIT_4_0_2026. Freeze the exact TPM, state, boundary, wiring, partition, purview and source. Actual large-N exact IIT remains uncomputed; cut-proxy numbers cannot discharge its MIP / CES.
- **D3B.4, physically measured neural experiment:** choose independent open neuronal state/functional recordings, measured connectivity/interventions, and a specific observer \`Q\` and target \`T\`; use periodic XOR as a mathematical null only.
- **D5, consciousness rival hypotheses:** compare GNWT, IIT, teleodynamics and relational qualia with preregistered matched consumers and no-report controls. No geometry→phenomenal theorem from rank or cut counts.
- **P6, magneto-optics/quantum:** keep Ferrocell physical field-response and putative coherence/entanglement/zero-point claims separate; no physical imports from XOR field algebra.

**Acceptance commands** (proposed; executing one does not imply all):
\`\`\`sh
python3 scripts/iit_lattice_prime_power_audit.py --json /tmp/iit-lattice-prime-power.json
python3 scripts/iit_ternary_lattice_scaling.py
python3 scripts/iit_lattice_scaling_experiment.py
python3 scripts/iit_xor_grid_two_step_audit.py
# with the pinned Agda dependencies:
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/EverythingIITPhiIntegrationMaxCut.agda
\`\`\`

**Phase verdict:** our earlier "recurrent XOR grid extinguishes itself" result is *correct only for the specified 2×2 source fixture*. An arbitrary larger recurrent XOR square **need not extinguish**. The higher-priority achievement is the source-versioned characteristic/dimension/size discriminator, not additional small truth-table enumeration.


### Symbolic million-site comparison added after the finite audit

The prime-power audit script now also emits **analytic, not executed-matrix** landmarks:
- \`n=1000\`, binary **periodic east-plus-south XOR**: \(N=1{,}000{,}000\), one-step \(\operatorname{rank} F=999{,}000\), \(\dim\ker F=1000\), and \(F\) is **not nilpotent** because side length 1000 has an odd factor. This is **not** Tononi's proposed physical majority-input gate configuration even though its spatial site count matches.
- \`n=1024=2^{10}\`, same **periodic XOR**: \(N=1{,}048{,}576\), one-step \(\operatorname{rank}F=1{,}047{,}552\), nullity \(1024\), and \(F^{1024}=0\) for every state by the characteristic-two Frobenius identity.

These are closed-form consequences, not physical measurements, not allocations of million-by-million transition matrices, and not full IIT computations. A **2.4% difference in side length** (1000 versus 1024) here changes the nilpotence class because arithmetic periodicity is part of the specified model; no inference about actual neural substrates or consciousness follows.


## 2026-10-24 D3B.5: 5³ lost five dimensions = one cyclic residual profile

**New exact model-derived result:** on the pre-existing ternary periodic **5×5×5 three-axis sum operator** \(F\), the rank-120/nullity-5 result admits a *canonical source-identity decomposition*, not merely five anonymous null directions. The lost kernel is \(J(\mathbb F_3^{\mathbb Z/5})\) where \(Jg(i,j,k)=g(i+j+k\pmod5)\). Each of five diagonal planes has 25 sites. Its extractor \(P(x)(s)\) sums that plane mod3. Thus \(PJ=1\), \(FJ=0\), \(PF=0\), and a full 125-basis arithmetic certificate verifies \(F^{80}=I-JP\).

This proves \(V=\operatorname{im}F\oplus\operatorname{im}J\), of dimensions **120+5=125**; \(F\) has reversible 80-period-dividing dynamics on the 120-dimensional retained core and loses the single *five-slot cyclic profile* at the first step. Reconstruction from the observed update and relative residual is \(x=F^{79}(Fx)+J(Px)\). This is a stronger, concrete producer for the existing \`JCoarse/JFine\` **consumer-relative reopening** machinery; geometrically one cyclic profile does not mean a literal fourth spatial axis or the arithmetic \(5^3+5=130\) source space. Note that \(P\) itself is a coarse geometric observation, while **in the dynamical consumer** \(F(x)\) is the coarse/retained observation and \(P(x)\) is its relative fine reopening residual. Those relative labels depend on the consumer.

**Primary owner and receipts:** [\`docs/superpowers/plans/2026-10-24-iit-5cube-jplusone-coarse-fine.md\`](./2026-10-24-iit-5cube-jplusone-coarse-fine.md); \`scripts/iit_j_coarse_fine_5cube_audit.py\`; \`DASHI/Biology/IITFiveCubeJCoarseFineRelativeBridgeExact.agda\`; numeric-regression integration. The source-written Agda bridge proves only the **conditional** reconstruction theorem from a supplied algebraic certificate, not a concrete 125-dimensional kernel theorem. Explicitly separates the original harmonic \(j_{\rm coarse}=9\) and \(j_{\rm fine}=19683\) from the new five-slot profile. Source provenance and historical IIT interpretation gates are unchanged.

**Anti-overgeneralization:** 3D F₃ periodic side n=3 has nullity 9 (rather than n=3); side 4 nullity 4; side 5 nullity 5. Another analytic counterexample at side 8 yields 56 zero eigenmodes using the 8-element \(\mathbb F_9^\times\) root spectrum. One-profile \`+1\` is a hypothesis local to the selected n=5 same-object model, not a universal dimensional law.
