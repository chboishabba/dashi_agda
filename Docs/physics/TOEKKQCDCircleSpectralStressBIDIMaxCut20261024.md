# TOE × KK × QED/QCD: same-operator and same-action Casimir max-cut
Date 2026-10-24. Canonical implementation branch: `lares2-kk-observable-maxcut-20261023`, PR #1241.

## Original-source attribution / ownership

- Arkani-Hamed, Cohen, Georgi, *(De)Constructing Dimensions*, **Phys Rev Lett 86 (2001) 4757–4761**, DOI **10.1103/PhysRevLett.86.4757**: original dimensional-deconstruction physics. Cycle Fourier diagonalisation, Wilson phases and finite-difference convergence are standard mathematics, NOT an original TOE discovery.
- Abe, Inami, Kawamura, Koyama, *Radion stabilization in the presence of Wilson line phase*, PTEP 073B04 (2014), DOI **10.1093/ptep/ptu097**: original one-loop compact-circle radion/Wilson Casimir work. DASHI's particular spectrum and model parameter choices are repo-authored conditional computational fixtures.
- Older Casimir stress prior art: Brown and Maclay, *Vacuum stress between conducting plates: an image solution*, Phys Rev 184 (1969) 1272–1279, DOI **10.1103/PhysRev.184.1272**; this is a parallel-plate U(1) benchmark and DOES NOT directly supply the periodic S1 KK/QCD energy tensor.
- Canonical repo geometry: **PR #1249** (inspected head f8663228f3eaa968cd772ea239a7085e36b07219) owns `scripts/check_hyperfabric_27_729_19683_refinement.py`, exact *P3^(3k)* path-graph refinement, Z2 covariant repair and plaquette-flux nontriviality. Its 27-minus-one quotient and c=26/worldsheet checks are different physical consumers.
- TOE realization and primitivity: **PR #1217**, inspected head 4a1f292ab50766dadf730017423250235c0ed3fd, owns `TOESectorRealizationExact`, `TOEGaugeQFTGRRealizationExact`, `TOEPrimitiveMaxCutExact`. Real action/metric variation, selected QFT stress and physical calibration remain explicitly UNPAID.
- Actual source-native Casimir and variation: **PR #1165**, inspected head bf959d7c338b4195b9304d8e05fae594f9464b13, owns the two primitive selected-QFT continuum/Schwinger receipts plus R114/R119/R122/R124/R127 same-operator/measure/stress chain. Its Brown–Maclay stress is NOT the complete QCD Casimir 5D stress.
- Current **PR #1241** inherits its own field-spectrum scripts, the QED+QCD vacuum stationarity obstruction `scripts/check_kk_qed_qcd_casimir_budget.py`, product source compatibility, scalar matching and BIDI/steelman. New files below are in THIS branch. Cross PR module paths are **provenance refs, not already typed imports or merged results**.

## BIDI-A: Which '27' realizes the KK fifth-direction operator?

These cardinalities cannot be identified merely by an arithmetic 27:
- `P3^3` original path cube: 27 sites, 54 edges, graph-Laplacian spectrum `{0:1,1:3,2:3,3:4,4:6,5:3,6:3,7:3,9:1}`.
- `C3^3` periodic three-axis torus: 27 sites, 81 edges, Laplacian spectrum `{0:1,3:6,6:12,9:8}`.
- `C27` single discretized spatial **circle**: 27 sites, 27 edges, degree two, 14 distinct eigenvalues rather than either spectrum above.

Moreover #1249's exact `P3^3 -> P3^6 -> P3^9` graph growth **adds independent axes** (dimensions 3,6,9). Its first nonzero Laplacian eigenvalue remains 1 but its multiplicity grows 3→6→9, whereas a smooth untwisted circle has first excited KK gap multiplicity 2 (`n=+1,-1`). The #1249 graph refinement therefore does not discretize a *fixed-dimensional* circle, even though 27/729/19683 counts may evoke KK or Monster dimensions.

`DASHI/Physics/Gravity/TOEKKCircleSpectrumConsumerBIDIExact.agda` uses canonical `FormalClaimTransportGeometryExact` and `ConsumerFibreRepairExact` to exhibit:
1. same cardinality 27, different selected physical Laplacian: cardinality cannot factor the chosen-operator consumer;
2. finite C27 Fourier character aliases `n=0` and `n=27` (same samples), whereas smooth b=1 KK mass squared differs `0` vs `729`: finite Fourier does NOT answer full unbounded KK tower consumer;
3. these failures do not invalidate finite-band math or selected lattice Fourier identities. Agda module SOURCE-WRITTEN/KERNEL UNVERIFIED.

## BIDI-B: Construct the actual operator lift required for KK

Choose N=3^k and sample **ONE S1 circle** of circumference `L=2pi*b` with spacing `a=L/N`. These are *new constant-dimension refinements*, not the same #1249 P3^(3k) graph.

For U(1) Wilson phase theta and alpha=theta/(2pi), set constant forward link `U=e^(i theta/N)`. The gauge-covariant scalar Laplacian on vertices j is

`(-D_N^2 f)_j=(2 f_j-U f_(j+1)-conj(U) f_(j-1))/a²`.

Fourier character `f_j=e^(2pi*i*n*j/N)` has exact physical eigenvalue

`lambda_(N,n,alpha)=(N/(pi*b))² sin²(pi*(n+alpha)/N)`.

The physical continuum twisted compact KK tower has

`lambda_(infty,n,alpha)=(n+alpha)²/b²`.

For fixed |n+alpha| and |pi(n+alpha)/N|<=1, the elementary sine bound gives

`0 <= lambda_inf - lambda_N <= pi²*(n+alpha)^4/(3*N²*b²)`.

For a **fixed low-frequency band** |n|<=K and proper-time/heat parameter t>0, termwise mean-value bound yields

`0 <= Sum_band(exp(-t lambda_N)-exp(-t lambda_inf)) <= [t*pi²/(3*N²*b²)] Sum_band(n+alpha)^4`.

The numerical script tests N=9,27,81,243,729 with alpha=0,0.17,0.5, K=3 and dimensionless b=1, and tests local U1 gauge conjugation and invariance of Wilson product ∏U=e^(i theta).

**Important:** This provides a rate-controlled *finite-band spectral and heat-trace* bridge. It does NOT establish the full renormalized Casimir energy, which depends on the unbounded KK tail, 4D momentum integral, counterterm scheme and ultraviolet regulator. A finite N simulator necessarily aliases mode n and n+N, so extrapolating this finite-band inequality to all n would be mathematically invalid. A physical deconstructed KK candidate requires its own action, link-field dynamics, gauge/matter spectrum, regulator and stress variation.

Executable: `python3 scripts/check_toe_kk_s1_ternary_spectral_bridge.py`. Independent Python reproduction of graph counts, exact finite-mode aliases, Wilson conjugation and fixed-band eigen/heat bound **PASSED**; the GitHub source was fetched/inspected but not byte-run from GitHub, hence no committed-head script-execution claim.

## BIDI-C: Exact 5D vacuum internal-pressure residue (TOE action/stress critical path)

For the selected Einstein-frame zero-mode effective potential

`V_E(x) = c0/b0^4 * [ell/x + W(x)/x^6]`, `x=b/b0`,

the physical Jordan frame inherited from 5D metric satisfies `g_E=(b/b0)g_J` and hence

`V_J=x² V_E = c0/b0^4 * [ell*x+W(x)/x^4]`.

For one flat compact 5D background, its renormalized Casimir energy per noncompact 3-volume is V_J. Variation with the actual circle length L=2pi*b defines

`rho_5=V_J/(2pi*b), p_5=-dV_J/d(2pi*b)`.

Minkowski tuning `V_E(1)=0` imposes `ell=-W(1)`, hence `rho_5(b0)=0`. But direct source-side variation yields the **exact** relation

`p_5(b0) = - [c0/(2pi*b0^5)] * [W'(1)-5W(1)]`.

This is precisely the QED/QCD same-radius stationarity residual already calculated in #1241. With the added periodic free gluon/quark sector, `D=W'-5W ≈ -240`, the retuned 4D vacuum has `rho_5=0` but `p_5>0`. A **strict flat GR×S1 5D product** has `G_AB=0` and requires vanishing total source, including `T55=0`. Thus the selected candidate FAILS 5D source compatibility despite being retuned to zero four-dimensional vacuum energy. The same problem cannot be repaired by cosmological tuning alone. This argument concerns a renormalized effective stress model; it is not full quantum 5D Einstein/source solution, QCD determinant or a universal KK no-go.

This weld improves upon a bare Casimir polynomial residual because it is *exactly a source-variation obstruction*, the primitive physical consumer sought by TOE #1217 and Casimir #1165. Neither gives an actual common quantum action, which remains OPEN.

Executable: `python3 scripts/check_toe_kk_qcd_internal_stress.py`. Independently executed SymPy derivation of the pressure/residual identity PASSED; no Agda kernel receipt.

## Max-cut priorities, Pareto ordered

1. **Highest:** pick a *physically admissible* QED+QCD+chiral-EW matter spectrum and compatible 5D action; derive its COMPLETE selected renormalized `W(b,theta)`, including gluon/quark content, holonomies, Wilson/radion Hessian, and apply both source and observable consumers. Do not hide quark zero modes behind a colour holonomy.
2. **Physical Casimir stress:** verify same-action 5D (T_{mu
u},T_{55}), counterterm variation, conserved matter current, and GR source equation, in the actual matter frame. Native #1165 QFT-stress compiler could consume that receipt if its continuum/Schwinger source assumptions are met; this result alone does not supply them.
3. **Operator refinement:** upgrade fixed-band (O(N^{-2})) cycle convergence to an admissible regulated heat kernel/determinant/stress with explicit UV subtraction and an error bound uniform in the regulator before using TOE hyperfabric as the physical compact dimension.
4. **Chiral/SM:** reconcile inherited charge-table (Q=T_3+Y) and SU3×SU2×U1 anomalies with an ACTUAL 5D compactified chiral sector; no full chirality generated on a plain free S1 Dirac zero mode. Existing finite anomaly sums are not a physical spectrum.
5. **Earth:** only after physical vacuum and material source are selected, derive rotating source, slow-spin metric and reproducible held-out satellite discriminator. Current extreme-short-range radion returns GR-like orbital behaviour, which may be a scientifically valid null.
6. **Others:** Monster 3B, 729-dimensional modules, 27−1/26 string bookkeeping, Alexander horned topology and Yang–Mills Clay estimates are valuable independent consumers but NOT the prerequisites for the chosen physical S1 QCD-Casimir calculation.

## Attribution/proof-status audit

- Original dimensional-deconstruction and Casimir/QCD physics: cited external primary roots, NOT new DASHI mathematical discovery.
- TOE/Hyperfabric/QFT stress theorem owners: existing respective GitHub PRs, NOT silently copied or promoted across unmerged branches.
- This PR: consumer-specific operator tests, exact restricted internal-pressure identity, formal finite non-descent witnesses, and explicit source/field-content residual.
- Local Python equivalent tests: PASS. Committed GitHub scripts source inspected, exact blob byte-execution NOT claimed.
- New Agda module: SOURCE-WRITTEN; no exact-head kernel receipt.
- No physical QFT path integral, continuum UV control, full Standard Model, complete rotating 5D Earth, or measured LARES-2 deviation proved.

Expected commands:
`python3 scripts/check_toe_kk_s1_ternary_spectral_bridge.py`
`python3 scripts/check_toe_kk_qcd_internal_stress.py`
`agda -i . DASHI/Physics/Gravity/TOEKKCircleSpectrumConsumerBIDIExact.agda`
