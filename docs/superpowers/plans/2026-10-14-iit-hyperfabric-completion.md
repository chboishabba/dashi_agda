# IIT Hyperfabric Completion Implementation Plan

> **For agentic workers:** use the repo's formal-development workflow. Formal completeness is established by the Agda aggregate and Agda kernel checking; Python is reserved for numerical / finite-combinatorial verification.

**Goal:** Complete the finite IIT-4 + hyperfabric programme from system-phi calibration through distinctions/relations/Phi and consumer-descent boundaries.

**Architecture:** Keep causal fabric `H`, local synthesis law `mu`, and state `s` independent. IIT partitions act on causal connections. Gate laws remain local to `(A,B)->C` cells. Graph, stalk-restriction, and global-section partition semantics remain distinct.

**Verification authorities:**

1. **Agda:** `agda DASHI/EverythingIITPhiIntegrationMaxCut.agda` is the authority for formal imports, theorem surfaces, type separation, and promotion firewalls.
2. **Python finite numerics:** `python scripts/iit_numeric_verification.py` is the authority only for executable finite IIT values and finite combinatorial counts.
3. **PyPhi:** `scripts/iit4_pyphi_oracle.py` is the external full-CES numerical oracle when a compatible PyPhi runtime is installed.

There are deliberately no Python source-presence checkers and no grep-based shell pseudo-proofs.

## Global constraints

- Reuse existing repo owners before introducing new algebra/topology definitions.
- Keep IIT 4.0 (2023) and the 2026 intrinsic-information requirement explicitly versioned.
- Do not identify historical IIT/XOR values with IIT-4 structure `Phi`.
- Do not identify 1->3 topological pants with 2->1 causal synthesis without an explicit reversal witness.
- Do not treat `C3^3` recentering as a canonical symmetry of the non-periodic ternary cube.
- Treat “369” as the repo's **3/6/9 algebra family plus ternary 27/composition geometry**, not merely the cardinality sequence `3^n`.
- Equal cardinality never licenses algebra identification (`Z6` versus `S3`, or `C9` versus `C3 x C3`).
- Never promote a Python numerical receipt to an Agda proof.
- Never claim Agda-green without an actual Agda/CI receipt.

---

## Task 1 — Versioned finite IIT-4 system kernel

**Owners:**
- `DASHI/Biology/IIT4FiniteExecutableKernelExact.agda`
- `scripts/iit4_finite_reference.py`

**Implemented surface:** finite factored TPMs, cause/effect specification, directional partitions, independent causal marginalisation of cut inputs per target factor, normalized MIP selection, unnormalized system `phi_s`, and separate 2023/2026 semantics.

**Numerical regression:** unified verifier checks 54 three-unit directional partitions, recurrent XOR/OR/AND/triXor, feed-forward controls, and the 2026 deterministic cap.

## Task 2 — XOR-grid calibration

**Owners:**
- `DASHI/Biology/IITXORGridFibreCalibrationExact.agda`
- `DASHI/Biology/IITXORGridFibreCircuitBridgeExact.agda`
- `scripts/iit_xor_grid_calibration.py`

The actual 2x2 repo fixture is represented as local XOR synthesis plus a separate recurrent gluing graph. Under the shared factored finite evaluator the 2023 statewise profile is `{0, 0.5}` with 12/16 zero states; deterministic 2026 `phi_s` is zero throughout.

## Task 3 — Matched fabric/gate sweeps

**Owners:**
- `DASHI/Biology/IITMatchedFabricGateExperimentExact.agda`
- `scripts/iit_matched_fabric_gate_sweep.py`

One shared numerical kernel evaluates both controlled axes:
- hold fabric fixed, vary XOR/OR/AND/triXor;
- hold XOR fixed, vary feed-forward/recurrent/grid fabric.

No second bespoke IIT evaluator is retained.

## Task 4 — 369 matched-algebra controls

**Owners:**
- `DASHI/Biology/IIT369MatchedAlgebraControlExact.agda`
- `DASHI/Biology/IIT369PantsGluingBridgeExact.agda`
- `DASHI/Foundations/HexTruthS3CarrierBridgeExact.agda`
- `DASHI/Foundations/PhaseQuotientNonaryGroupSeparationExact.agda`
- `scripts/iit_369_algebra_scan.py`

This is deliberately not just a `3^n` test. Two same-cardinality controls are first-class:

- **Six states:** `HexTruth`/cyclic `Z6`-like addition versus the noncommutative `S3` permutation product. The repo owns an exact six-state carrier chart and proves that it cannot preserve both products. The matched recurrent numerical fixture observes the same IIT-4 (2023) system-phi profile `log2(36)` for both.
- **Nine states:** cyclic `C9`/NonaryTruth addition versus `C3 x C3` / `F3^2` componentwise addition. The repo proves the group laws are not isomorphic; the matched recurrent numerical fixture observes the same 2023 system-phi profile `log2(81)` for both.

These are consumer/non-identifiability results for the tested IIT observation. The numerical collisions are not the algebraic separation proofs.

## Task 5 — Path-indexed pants / hyperfabric fixtures

**Owners:**
- `DASHI/Biology/IITHyperfabricCausalCellNetworkExact.agda`
- `DASHI/Reasoning/IITHyperfabricPartitionBridgeExact.agda`
- `scripts/iit_hyperfabric_fixture_scan.py`

Local synthesis, gluing path, typed seam compatibility, and partition semantics remain separate coordinates. Numerical scanning currently evaluates graph-level causal partitions only; stalk/global-section obligations remain formal typed surfaces.

## Task 6 — Pointed ternary-27 gluing envelope

**Owners:**
- `DASHI/Biology/IITPointed27HyperformExperimentExact.agda`
- pointed-27 / origin+26 / recentered-26 / cyclotomic / triadic non-descent owners
- `scripts/iit_pointed27_gluing_scan.py`

The numerical/combinatorial layer checks the exact finite incidence envelope: 27 points, strata `1+6+12+8`, 54 point-face incidences, six 9-point faces, twelve 3-point face-pair overlaps, eight one-point corner triples, and `27^3` three-selected-cubie choices. Geometry alone does not manufacture a TPM.

## Task 7 — Distinctions, relations, and structure Phi

**Owners:**
- `DASHI/Biology/IIT4FiniteDistinctionExact.agda`
- `DASHI/Biology/IIT4FiniteRelationExact.agda`
- `DASHI/Biology/IIT4FiniteCauseEffectStructureExact.agda`
- `scripts/iit4_structure_reference.py`
- `scripts/iit4_pyphi_oracle.py`

`phi_s`, `phi_d`, `phi_r`, and structure `Phi` remain separate typed quantities. The lightweight Python structure reference verifies arithmetic/combinatorics only; the PyPhi adapter is the external source-faithful full-CES numerical route and records runtime package provenance separately from the calibration source revision.

## Task 8 — XOR / 369 stress family

**Owners:**
- `DASHI/Biology/IITXOR369StressFamilyExact.agda`
- `scripts/iit_xor_369_stress_scan.py`

Stress comparisons are versioned and alphabet-aware and include binary XOR, ternary triXor, six-state `Z6/S3`, and nine-state `C9/F3^2` controls. System-phi ordering is never promoted to a consciousness ordering or silently identified with big-Phi.

## Task 9 — Consumer descent

**Owner:** `DASHI/Biology/IITIIT4ConsumerDescentExact.agda` plus existing consumer-descent / brain / MaleCNS owners.

This task is formal, not a Python truth table. Exact non-descent witnesses include same-cardinality observations losing algebra identity and selected ternary-27 cubies losing the irreducible triadic face. The numerical verifier may report observed IIT collisions, but consumer factorisation claims are owned by Agda.

## Task 10 — Aggregate and verification loop

**Owners:**
- `DASHI/Biology/IITHyperfabricCompletionReceiptExact.agda`
- `DASHI/Biology/IITPhiIntegrationEverything.agda`
- `DASHI/Biology/IITPhiIntegrationMaxCutValidation.agda`
- `DASHI/EverythingIITPhiIntegrationMaxCut.agda`
- `scripts/iit_numeric_verification.py`
- `.github/workflows/iit-phi-integration-maxcut.yml`

The completion ledger separates source presence, numerical-program presence/execution, PyPhi-oracle execution, and Agda-kernel execution. It does not let one authority substitute for another. The workflow has separate numeric and Agda jobs and contains no source-grep pseudo-proof.

## Acceptance sequence

Run in a suitable checkout:

```bash
python scripts/iit_numeric_verification.py
python scripts/iit4_pyphi_oracle.py --help   # then run selected full-CES fixtures with installed PyPhi
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/EverythingIITPhiIntegrationMaxCut.agda
```

The first command establishes finite numerical/combinatorial regression targets only. A fresh PyPhi oracle run establishes full-CES numerical values for selected fixtures. The final command (or equivalent CI kernel evidence) establishes formal Agda validity.


## Task 11 — XOR-grid recurrence-versus-dynamics counterexample (2026-10-24)

**Reason for cut:** The XOR-grid model's causal wiring has directed cycles, but the selected linear Boolean dynamics **erase every initial condition after two updates**. This is a source-derived fact stronger than a generic "network topology differs from local gate" boundary. It is a check against treating recurrent connectivity, C3 port holonomy, graph cut, instantaneous \`phi_s\`, lasting information, or phenomenal consciousness as interchangeable.

**Original owners and priority:** reuse \`IITXORGridAdversarialExact.gridStep\` and the exact \`IITXORGridFibreCircuitBridgeExact.northWestNorthEastCircuit\`. New bounded DASHI consequence in \`IITXORGridTwoStepDynamicsExact.agda\`, wired into \`IITPhiIntegrationEverything.agda\`; independent executable enumeration \`scripts/iit_xor_grid_two_step_audit.py\` imports the canonical numerical \`grid2x2_step\` instead of reimplementing the grid.

With \`x=(NW,NE,SW,SE)∈F₂⁴\`:
\`\`\`
F(x) = (NE⊕SW, NW⊕SE, NW⊕SE, NE⊕SW)
F²(x) = (0,0,0,0)          for every one of the 16 possible x
Im(F) = {(p,q,q,p) : p,q∈F₂}     exactly 4 outcomes
each image outcome has 4 preimages
\`\`\`
This is a **nilpotent index-2** state transition despite genuine directed 2-edge circuits. A state has no nonzero periodic orbit under this chosen map. The statement is about the small *DASHI fixture*, not arbitrary square grids or the entire class of physically implemented XOR systems.

**Independent checked toy enumeration:** all 16 states, 4 one-step outputs (4 preimages per output), all second iterates zero; computed with a separate 2026-10-24 Python enumeration. **Actual exact-head PR script run and Agda kernel check remain separate pending receipts** in this environment.

**Source origins (keep distinct):**
- Scott Aaronson, "Why I Am Not An Integrated Information Theorist (or, The Unconscious Expander)" and follow-up critique, *Shtetl-Optimized* (2014), \`https://scottaaronson.blog/?m=201405\`. Original critic, not author of DASHI's 2×2 computational proof.
- Giulio Tononi, "Why Scott should stare at a blank wall and reconsider (or, the conscious grid)" (2014), \`https://learniit.org/corpus/tononi-2014a\`. Direct response defends the IIT interpretation of constructed XOR grids; do not attribute that view to Aaronson.
- Larissa Albantakis et al., "Integrated information theory (IIT) 4.0: Formulating the properties of phenomenal existence in physical terms", *PLoS Computational Biology* 19(10), e1011465 (2023), DOI \`10.1371/journal.pcbi.1011465\`. IIT's original 2023 formal model, not proof of phenomenal identity in the DASHI grid.
- Current PyPhi formalism \`https://pyphi.readthedocs.io/en/latest/theory/formalism-versions.html\`: 2023 versus 2026 system-phi definitions must be versioned. Its documented canonical three-XOR example gives 2023 \`phi_s=1.5\` versus 2026 \`phi_s=0\` (different from the 2x2 grid), while cause–effect structure can remain nonempty. Under the repo's 2x2 numerical reference: 2023 \`phi_s∈{0,0.5}\`, positive at 4/16 states, and 2026 \`phi_s=0\` at all 16 states. **These are numerical-source/reference results, not Agda theorems or claims of consciousness.**

**Cross-PR source boundary:** The consumer-relative geometry/learning crosslinks in [#1246](https://github.com/chboishabba/dashi_agda/pull/1246) (Ferrocell/qualia roadmap), [#1095](https://github.com/chboishabba/dashi_agda/pull/1095) (semantic-action geometric reasoning), and [dashiBRAIN #7](https://github.com/chboishabba/dashiBRAIN/pull/7) remain sibling branches. No unmerged module is imported or reported as merged. The XOR grid informs **experimental null design**, not a realised correspondence between neurons, ferrofluid, quantum entanglement or a phenomenological field.

**Acceptance (on this exact IIT branch, with pinned dependencies):**
\`\`\`sh
python3 scripts/iit_xor_grid_two_step_audit.py
python3 scripts/iit_xor_grid_calibration.py
python3 scripts/iit_numeric_verification.py
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/EverythingIITPhiIntegrationMaxCut.agda
\`\`\`
Required receipts: full branch commit, stdout/exit status, toolchain, numeric formalism version, input/source digest, and any failing dependency. A source-written Agda proof is not a passed compiler run; finite recurrent-state dynamics do not independently settle IIT's interpretive premises.


## Task 12 — Large-grid correction / prime-power exact dynamics (2026-10-24)

**Canonical source-and-result audit:** [\`docs/superpowers/plans/2026-10-24-iit-large-grid-original-comparison.md\`](./2026-10-24-iit-large-grid-original-comparison.md).

The 2×2 nilpotence theorem added in Task 11 is **not a universal recurrent XOR-grid theorem**. The already existing \`iit_lattice_scaling_experiment.py\` / \`iit_ternary_lattice_scaling.py\` cover **2D n=2..10 (100 sites)** and **3D n=2..5 (125 sites)** over F₂/F₃, computing exact linear-algebra ranks and declared-slab cut proxies, **not large-grid exact IIT Phi**.

With periodic \`F = sum S_i\` over F_p and \`n=p^k\`, characteristic-p Frobenius gives \`F^n=(d mod p)I\` for d coordinate directions. So binary 2D 4×4/8×8 extinguish but binary 3D 4³ is periodic/invertible; ternary 2D 3×3 has \`F³=-I\`, while ternary 3D 3³ extinguishes at \`F³=0\`. The previously owned \`IITCubeConcreteTorusImageExact.bop3Neg\` is reused in source-written \`IITLatticePrimePowerSourceBridgeExact\`, with six-step identity and injectivity as finite Agda candidate results. **No new general Agda kernel receipt claimed.**

Independent local Python arithmetic checked **26 size/field/dimension cases**, with **eight prime-power matrix identities on every basis vector**. On the IIT branch the newly committed \`scripts/iit_lattice_prime_power_audit.py\` is also called by \`scripts/iit_numeric_verification.py\`, but an exact GitHub checkout execution and Agda kernel execution still need separate receipts. **Time-dependent state loss is not inferred from one-step kernel dimension.**

Original 2014 source correction: Tononi's illustrative physically realised lattice used **e.g. majority-input gate rules** on a hypothetical **1000×1000** grid. DASHI's cyclic east+south sum is a mathematical alternative, not that physical example or a computation of its complete IIT 3.0 conceptual structure. Its analytic 1000×1000 binary rank formula is *extrapolation*, not an executed million-node experiment. Historical IIT 3.0, IIT 4.0 2023 and IIT 4.0 2026 must remain distinct.

Remaining frontier: match actual spatial wiring and gate/TPM to the historical theory's premises (if that reproduction is worth computational expense); pin theory version, partition/causal noising and state; run source-faithful full CES at tractable sizes; then measure scaling bounds rather than substituting geometric slab counts for Phi. Prioritize calibrated neural/memory/AI consumers over new 27-cardinality scans or another Boolean truth table.


## Task 14 — 3^9 as 3^4 · 3 · 3^4, S3/zeta and Monster C3 character (2026-10-24)

**Owner:** [full source audit](./2026-10-24-iit-jfine-4-1-4-s3-zeta-gauge.md). Reuse the pre-existing actual nine-trit FineFrequency phase table and the recentered ternary S3 source. Two new Agda modules, IITJFineFourOneFourS3ZetaGaugeExact and IITJFineS3RegularMonsterCharacterExact, construct the literal four corners / distinguished centre / four edge codec, subtract the centre from each of the eight outer values, and express the exact global affine S3 action on that coordinate space. The latter module reconstructs the original pointed 10×19683 harmonic source as a **free C3-set with 65610 orbits**, matching the *C3 character* of the Monster3BRegularC3BulkResidualFiftyThreeBidiExact regular summand.

Finite local arithmetic confirmed 19683 two-sided configurations, 118098 S3 equations, orbit sizes 1×3 and 3280×6, and complex S3 irreducible multiplicities on the pointed model **32810·triv + 32800·sign + 65610·Std2**. Restriction to C3 gives three sectors of size 65610, matching \(W|C3=53·1+65610·Reg(C3)\) on the 196830-dimensional regular part only. This is a genuine source-specific **character** comparison, not a chosen literal Monster W module map; exact-head Agda kernel compilation and source-action normalizer comparison remain necessary.

Do not confuse the **value** S3 with site D4, chosen five-position C5, original F4 zeta, F81 characteristic-three arithmetic, or the Riemann zeta function. In characteristic3 the polynomial X³−1=(X−1)³ gives no distinct zeta roots; the three eigenspaces refer to characteristic-zero linearisation. Two four-trit blocks are abstractly 81-state fields if separately equipped with multiplication but have different D4 mirror characters (2 vs 0 fixed sites). Numeric verifier imports the new finite audit; user requested local Python over CI and no CI status is claimed.
