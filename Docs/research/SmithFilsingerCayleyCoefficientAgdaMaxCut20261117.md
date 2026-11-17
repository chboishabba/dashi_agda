# Smith/Filsinger F13 exact rational Cayley-to-Agda reachability weld — 17 November 2026

## Original owners reused and key remaining gate

PR #1524 already has `SmithFilsingerLocalCausalADEFrameExact.LocalPrimitive` and `SmithFilsingerLocalCausalADEReachExact.ZeroPreserving` / `noSignalOutsideInterleavedSourceCone`. Its source-owned `scripts/smith_filsinger_local_causal_ade_sympy.py` actually executes rational midpoint/Cayley steps for heterogeneous Maxwell curl, polarization and dissipative scalar edges. The previous Agda dynamic theorem was parametric and had only an unrelated additive zero-preserving fixture. The next max-cut is the **actual midpoint coefficient-to-Agda interface**.

## New Agda proof source

`DASHI/Physics/Motors/SmithFilsingerLocalCayleyZeroWeldExact.agda` imports BOTH exact existing Agda owners. It defines a contentful `CertifiedCayley`:

- `step, firstCoupling, secondCoupling, inverseDenominator, quarter : ℚ`
- `quarterIsQuarter`: four times `quarter` equals 1.
- `inverseLaw`: `(1 - quarter*h²*a*b)*inverseDenominator = 1`.

The two outputs are the EXACT off-diagonal 2×2 rational Cayley formula for `A=[[0,a],[b,0]]`:

[
T_h=(I-hA/2)^{-1}(I+hA/2)
= q\begin{pmatrix}1+h^2ab/4&ha\\hb&1+h^2ab/4\end{pmatrix},
quad q(1-h^2ab/4)=1.
]

`sameCayleyFirstZero` and `sameCayleySecondZero` use the repo's established rational ring solver, then `sameCayleyZeroPreserving` constructs the ORIGINAL Agda `Reach.ZeroPreserving` witness, and `sameCayleyGuarded` / `sameCayleyReachEvent` consume it. `DistinctCayleyEdge` additionally carries proof that the two endpoint IDs differ; coincident IDs would be unsound for the original priority-based two-output `Frame.applyPrimitive` matrix semantics.

Real Ohmic, material relaxation, and useful-load edges are **diagonal**. `CertifiedDiagonalCayley` supplies the exact midpoint factor `(1+hλ/2)/(1-hλ/2)` and its nonzero-denominator certificate; `diagonalCayleyZero` proves its zero-preserving law. `diagonalFrameZeroPreserving` represents it as a one-coordinate change with the other coordinate retained. A selected source-owned Cayley step becomes a typed `Reach.LocalEvent`, while `singleCayleyWithSourceNoSignalOutsideReach` explicitly consumes the existing all-N interleaved source theorem, including a separately tagged natural/controller injection.

This is a substantive matrix-coefficient-to-reachability bridge rather than a duplicate Green theorem. It does **not** yet prove the full 2×2 matrix identity inside Agda from `inverseLaw` (that algebra is independently checked by exact SymPy), nor inhabit the certificates for every arbitrary physical timestep; it is a source-authored, conditional theorem candidate pending pinned Agda acceptance. A diagonal step's unused endpoint must be distinct for faithful one-coordinate semantics.

## Exact regression

New `scripts/test_smith_filsinger_cayley_coefficients_sympy.py` checks the ACTUAL existing heterogeneous ADE edge generator `edge_updates` against the explicit Cayley coefficient formula for n=1..5, all its off-diagonal curl/memory edges, and its one-coordinate damping/receiver edges. It checks:
- exact equality with SymPy's direct `(I-hA/2)^{-1}(I+hA/2)` and zero-to-zero response;
- exact midpoint equation for nontrivial rational coefficients;
- singular denominator fails an inverse-certificate criterion (SymPy returns undefined `zoo`, not a valid field value);
- a later controller injection is seeded separately from the original natural source;
- zero field with all passive/local updates remains zero.

**Local exact pytest result:** 154/154 PASS (previous 138 + 16 new cases), SymPy 1.14.0 / pytest 9.0.2; run against the mounted prior 138-case package with the new exact test file. Not a completed GitHub-head CI receipt.

`scripts/check_smith_filsinger_formal_weld_agda29.sh` now includes the new Agda module in both `owners` and `new_owners`. `scripts/check_smith_filsinger_sympy_gate.py` requires its named theorem surfaces AND executes the new test; `scripts/check_smith_filsinger_dynamic_replenishment.sh` includes the same exact test. No ESD sources changed.

## Strict max-cut boundary

**D1 pinned Agda 2.9:** OPEN — no local Agda/Nix executable available, no kernel receipt. Static name/hole/regex checks and SymPy arithmetic are not Agda typechecking, nor proof of all imported owner modules.

**F13 physical Maxwell Green:** OPEN — finite local spectral and ADE work + zero-preservation do not establish a continuum 3D retarded front, calibrated anisotropic layers or actual collector/return field integration.

**F15 original independent replenishment:** OPEN — no calibrated same-original natural source, all controller/material losses or restored observed cycles. The user-origin Smith/Filsinger Sun–Earth harvesting hypothesis is not inferred from a zero-preserving Cayley matrix.

### Next high-alpha formal cut
Close the Agda 2.9 compiler errors on this exact source and derive the full two-variable Cayley midpoint matrix equation internally using the certified inverse law, `quarterIsQuarter` and the repository's rational ring solver. Then weld the actual heterogeneous cell IDs to the certified edge proof, and the source/receiver physical Maxwell admissions only when real source data exist.
