# F13/F15 — local causal Maxwell/Lorentz ADE and heterogeneous layers
**17 November 2026 · source-first continuation of PR #1524**

## What is genuinely new

The existing `smith_filsinger_lorentz_ade_sympy.py` proof owner has an exact energy-conserving implicit midpoint update. However, it uses an inverse of the full spatially coupled matrix. That operator is generally dense, so the output at a remote cell may depend on a source after one **numerical** step. Its causal use of a current time sample does not establish a finite spatial dependency cone, much less a continuum Maxwell light cone.

New `scripts/smith_filsinger_local_causal_ade_sympy.py` reuses the actual `LorentzMaterial`, `curl_matrix` and `energy` from the original ADE owner. The state is the same `z=(E,H,P,V)`. Unlike global implicit midpoint, it decomposes the original generator into *primitive spatially local* pieces:

1. one curl coupling between `E_i` and `H_j` for each nonzero original curl entry `C_ij`, using the real, per-cell `eps_i` and `mu_j`;
2. local electric–polarization momentum `E_i,V_i`, and polarization potential–momentum `P_i,V_i` coupling;
3. separate local Ohmic heat, Lorentz relaxation and physically useful receiver load conductance;
4. local natural and controller current kicks, which do not touch other cells.

A primitive two-coordinate generator `A_e` is updated using its own exact rational Cayley map

\[
T_e(h)=(I-hA_e/2)^{-1}(I+hA_e/2).
\]

Only the two active coordinates are solved; no global spatial inverse is constructed. The weights in the positive storage matrix are per-cell:

\[
M=\mathrm{diag}(\epsilon_i,\mu_i,\omega_{0,i}^2/\alpha_i,1/\alpha_i).
\]

For each primitive, the checked discrete identity is

\[
U(T_ez)-U(z)
=\frac{h}{2}\bar z^T(A_e^TM+MA_e)\bar z .
\]

Conservative curl and polarization primitives give exactly zero energy change. Passive Ohmic, relaxation and load primitives have a nonpositive change, and each signed natural/controller source kick pays exactly its own energy difference through the midpoint electric field. Composition gives the exact full ledger:

\[
\boxed{\Delta U+W_{\mathrm{useful}}+Q_{\mathrm{Ohmic}}
+Q_{\mathrm{Lorentz}}=W_{\mathrm{natural}}+W_{\mathrm{controller}}.}
\]

This is a finite semi-discrete splitting scheme, **not** a claim that one primitive equals a whole physical Maxwell timestep or exactly reproduces the original full-matrix implicit midpoint numerical result.

## Discrete causal dependency cone

Each stage has a **declared two-coordinate support**. The Boolean dependency set starts at the source coordinate and expands only when the current primitive touches an already dependent coordinate. The new `dependency_cone` proves/validates exact zero response outside this finitely generated set for zero initial state, even across a sequence of noncommuting updates.

A deliberate negative comparison uses the actual original global implicit midpoint: on a four-cell finite curl chain, a current applied at the last cell produces a nonzero far-cell tail after one full inverse; the strictly local scheme does not. That distinction is *numerical dependency support*, not an observable superluminal physical signal. The continuum Maxwell front and material geometry still require a separate sourced, measured or analytic admission, consistent with `SmithFilsingerYeeCFLConeGuardExact`.

**Caution:** a whole macro-step comprising many primitive updates can traverse multiple edges. The locality bound counts the actual primitive update sequence; it cannot be silently relabelled as one physical dt with a claimed speed c.

## Heterogeneous soil–air–ionosphere materials

The original local producer was extended with a `layers` vector of individually validated material objects. Each cell gets its own \(\epsilon,\mu,\sigma,\alpha,\gamma,\omega_0^2\). The Maxwell edge `E_i ↔ H_j` uses precisely the \(\epsilon_i,\mu_j\) pair, guaranteeing **same weighted curl cancellation across material discontinuities**; polarization and damping use the matching cell's own coefficients. This repairs the earlier uniform-mass assumption and removes the need to identify soil, air and ionosphere as one homogeneous dielectric.

Tests cover 3, 4 and 5 independently parameterized layers, reject a missing layer/negative damping, and preserve exact passivity and source work.

The values are **rational mathematical fixtures**, not independently measured conductivity profiles, actual terrain/electrode geometry, frequency-dependent tilted Hall/Pedersen ionosphere, atmospheric source or calibrated receiver.

## F15 physical accounting

The new `full_ledger` is a full consecutive-history consumer of actual primitive receipts. It separately accumulates signed natural source work, controller work, useful load, Ohmic and Lorentz relaxation, and exact stored energy change. It rejects disjoint/forged histories and unbalanced work. With both external sources off, a precharged receiver can deliver a transient load only by decreasing storage, not by being independently replenished.

Both `physical_source_meter=False` and `physical_maxwell_front=False` are explicit. In particular, choosing a positive test source current in the mathematical model cannot establish availability of natural Sun–Earth power. Actual source replenishment must be independently measured over a fully restored same-original environmental/controller/receiver/material cycle, with suitable error bars.

## Tests and acceptance

New source:
- `scripts/smith_filsinger_local_causal_ade_sympy.py`
- `scripts/test_smith_filsinger_local_causal_ade_sympy.py`

Added to the existing `scripts/check_smith_filsinger_dynamic_replenishment.sh` and the independent `scripts/check_smith_filsinger_sympy_gate.py`, which is in the pinned SymPy workflow. **Local exact SymPy/pytest: 131/131 PASS**, comprising the previous 112 and 19 new local/heterogeneous causal-work cases. All 19 local tests passed with SymPy 1.14.0 and pytest 9.0.2. The full suite was executed from the local source-equivalent working copy. This is not a completed GitHub-head CI receipt.

D1 is unchanged: the true pinned Agda 2.9 workflow must typecheck the Agda proof graph. An exact SymPy regression cannot prove Agda soundness, termination, coverage or the physical Maxwell source. No ESD surface edits.

## High-alpha next gates

**F13:** (a) formalize the primitive finite-support induction in Agda, reusing the existing indexed-face/finite chain owners; (b) a genuine physical-speed support theorem from a calibrated 3D Maxwell plus dispersive material differential operator, not merely a numeric graph cone; (c) layer interface and open radiation with actual 3D geometry, oblique anisotropy, full causal Green and electrode-return terminal including displacement current.

**F15:** independently measured external source and receiver signed powers, all material/ionization/modulator work, source backaction and full same-original environment state restoration. Check a robust gain ratio with upper/lower meter bounds, not a synthetic forcing trajectory.

**D1:** pinned Agda 2.9 CI/actual kernel acceptance and source-level repairs against any compiler errors. Continue to keep independent SymPy acceptance separate.

All previous Smith/Filsinger attribution and source-first gates preserved.


## Agda structural frame theorem: first kernel candidate

New `DASHI/Physics/Motors/SmithFilsingerLocalCausalADEFrameExact.agda` imports the CANONICAL `IndexedFaceIncidenceExact.sameID` and defines explicit primitive two-coordinate updates. `outsidePrimitive` shows a coordinate distinct from both endpoint IDs is unchanged; the `OutsideEvery` receipt covers **every stage in the actual finite list**. `neverTouchedRetainsOriginal` proves by induction that any coordinate outside all update endpoints retains its initial state across arbitrary noncommuting finite stages.

This is a bona fide finite frame theorem candidate with no added postulates or explicit holes. It is intentionally weaker than the full *dynamic* dependency-cone theorem: a touched coordinate can become nonzero only if its update actually depends on a previously activated endpoint, which the Python `dependency_cone` tests but this Agda module does not yet prove universally. No such theorem is promoted as a Maxwell front-speed result.

The new source is included in `scripts/check_smith_filsinger_formal_weld_agda29.sh`, which must be executed on an actual pinned Agda 2.9 host. Its kernel acceptance is OPEN in this session.

## Final tested receipt

The existing 112 local exact tests, 15 new primitive-local/dense-inverse controls, and four new per-cell heterogeneous material/negative controls give **131/131 PASS** using SymPy 1.14.0 and pytest 9.0.2. A single runnable ZIP was locally produced from the eighteen exact source/test files, with no undocumented physics input. This is local exact arithmetic, not a GitHub-head CI or Agda proof receipt.
