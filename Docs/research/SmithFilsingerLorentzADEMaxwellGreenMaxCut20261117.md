# Smith/Filsinger F13/F15 — causal Lorentz material and Maxwell Green weld
**17 November 2026 · PR #1524 · source-first exact mathematics; physical gates remain OPEN**

## Reuse, not a new Green ontology

The existing owners are SmithFilsingerDispersiveMaterialPortExact (all material/source ports), SmithFilsingerDispersiveMaterialWeldExact (same original and all-stores-return law), SmithFilsingerSpaceTimePoyntingTelescopeExact (signed work), the Balaban finite Green, and the already checked oblique/tangential Maxwell and passive radiation SymPy producers. They remain unchanged. This round builds the missing concrete passive constitutive source beneath them rather than reasserting their aggregate energy ledger.

## F13 finite Lorentz-ADE Maxwell source

New scripts/smith_filsinger_lorentz_ade_sympy.py supplies finite E,H,P,V cell vectors with a discrete curl matrix C:

- eps_inf E' = C H − sigma E − V + J_natural + J_controller − g_load E
- mu H' = −C.T E
- P' = V
- V' = alpha E − gamma V − omega0² P

For eps_inf, mu, alpha, omega0² strictly positive and sigma, gamma, g_load nonnegative, storage is U = (eps_inf |E|² + mu |H|² + (|V|² + omega0² |P|²)/alpha)/2.

The actual rational implicit-midpoint state update (not merely a user-selected ledger) satisfies:

**delta U + W_useful + Q_ohmic + Q_Lorentz = W_natural + W_controller**

where W_useful = h*g_load*|E_mid|², Q_ohmic = h*sigma*|E_mid|² and Q_Lorentz = h*gamma*|V_mid|²/alpha. The matrix generator obeys an exact dissipative quadratic-form identity, and the curl work cancels internally by using the same discrete C and C.T. Separate receiver work is not counted as material heat. Zero source with initially stored energy can pay a transient load only by depleting storage.

**These are exact finite Galerkin/material fixture results, not a physical SI Yee grid or a calibrated environmental source.**

## F13 material impulse, spectral correspondence and passivity

The same ODE gives susceptibility chi(s) = alpha/(s²+gamma*s+omega0²) and epsilon_eff(s) = eps_inf + sigma/s + chi(s). With strict damping gamma>0 and underdamping 4*omega0²>gamma², the tested causal material impulse is zero before time zero and, afterward, equals alpha*exp(−gamma*t/2)*sin(omega_d*t)/omega_d with omega_d²=omega0²−gamma²/4.

The tests verify its differential equation, correct impulse initial derivative, exact Laplace transform equals chi(s), and stable poles −gamma/2 ± i*omega_d. This proves **local temporal material causality**, NOT Maxwell spatial light-cone support.

The second new owner, scripts/smith_filsinger_lorentz_maxwell_weld_sympy.py, sends exactly epsilon_eff(−i*omega) into the existing oblique Maxwell generator and certified passive outgoing-radiation branch. It proves the identity:

omega*Im(epsilon_eff) = sigma + (gamma/alpha)*omega²*|chi(omega)|²

and the corresponding exact normal-incidence Maxwell Poynting dissipation matrix. This is a real cross-owner check: if Ohmic conductivity were also added as a second imaginary dielectric or material loss, the work budget would double count it.

## F15 full state return and conditional work

A new synthetic_cycle_work_receipt accumulates actual consecutive source-driven midpoint steps and their separate natural/controller/load/Ohmic/relaxation works. It rejects missing step identities, nonconsecutive full states and an aggregate energy mismatch; it requires *all* E/H/P/V components to match the initial state before reporting restored_all_4n_states=True.

An exact five-step example solves the forcing currents necessary to restore a nonzero state with positive useful receiver work and positive dissipation. Its source power is algebraically sufficient. It remains labelled original_source_meter_present=False and physically_replenished_source_certified=False. A zero-source transient discharge and a deliberately forged nonconsecutive history are negative controls.

The pre-existing Agda material-donor and same-original weld remain the golden physical admission owners. No finite source witness is promoted to a measured solar or atmospheric replenishment receipt.

## D1 independent verification, not an Agda substitute

Added the four source/test files:
- scripts/smith_filsinger_lorentz_ade_sympy.py
- scripts/test_smith_filsinger_lorentz_ade_sympy.py
- scripts/smith_filsinger_lorentz_maxwell_weld_sympy.py
- scripts/test_smith_filsinger_lorentz_maxwell_weld_sympy.py

Both new tests are wired to scripts/check_smith_filsinger_dynamic_replenishment.sh and the separate fail-closed scripts/check_smith_filsinger_sympy_gate.py. Local combined source-equivalent exact pytest: **112/112 PASS** (68 previous spectral Green + 44 new ADE/material/Maxwell/cycle checks), SymPy 1.14.0 and pytest 9.0.2. The independent SymPy CI workflow already exists and is retained; its execution on the newest PR head is not presumed to have passed. The real pinned Agda 2.9 kernel remains NOT VERIFIED.

## Exact next gates

1. F13: Real 3D spatially retarded Maxwell Green/light-cone theorem for measured dispersive and tensor Hall/Pedersen/parallel layers, appropriate open/radiation boundaries and independent original collector-ground return current.
2. F15: Independently calibrated natural source under receiver/controller backaction, separated real source/driver/modulator/loss meter receipts, restoration of source as well as receiver and material states, with uncertainty envelopes and repeatability.
3. D1: Run pinned Agda checker on the exact PR head, fix any type/termination/coverage errors. A SymPy identity is not a kernel proof.
4. F14/F16: Original device regime and atmospheric/cooling causal evidence remain distinct downstream gates.

Provenance: standard Lorentz/Maxwell passive material mathematics combined with existing DASHI source/port/Green owners; the Sun–Earth source/sink/Filsinger harvesting hypothesis remains user-origin and unverified. No ESD file edits or premature TOE promotion.
