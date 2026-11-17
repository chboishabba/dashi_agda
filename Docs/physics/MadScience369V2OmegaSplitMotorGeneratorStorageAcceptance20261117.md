# Ω stationary factorial measurement correction: two independently inventoried energy stores

**Status:** model-level exact energy and regression result; no original @madscience369 V2 measurements. This short repository acceptance memo accompanies the downloadable tested source archive. The original sixteen strong P0–P4 device obligations remain open.

## Correct physical contract

The previous factorial acceptor used a motor split with zero motor-side storage. That assumption is not generally valid. Let all oriented powers be positive in the declared direction and let the motor and generator side store energy separately. Then

\[
P_m=P_s+D_m+\dot E_m,\qquad
P_s+P_a=P_l+P_o+D_g+\dot E_g.
\]

Their sum is

\[
P_m+P_a=P_l+P_o+D_m+D_g+\dot E_m+\dot E_g.
\]

The transfer term \(P_s\) cancels **once**, rather than becoming an additional input. The identities are exact finite rational algebra; they do not establish that any real device has a complete measured source boundary.

## Strong negative control

One constructed 1 s observation has: motor input 286 W; shaft work 201 W; motor loss 86 W; motor stored energy decreasing from 100 J to 99 J; generator dissipation 201 W. Both split balances and the summed balance are exactly zero-residual. Yet this observation is NOT stationary, so the new protocol rejects it unless the motor storage change is independently admitted and explicitly included. The old motor split would fail or falsely suggest changed motor losses.

## Conditional experiment acceptance

Cross load off/on and recovery off/on in four predeclared arms; repeat each twice in a balanced eight-run palindrome per block. The blank 32-run template covers four blocks. The acceptor demands independent motor/generator stored-energy endpoints, shaft power, input, output, auxiliary and **independently measured** motor and generator losses, all with deterministic uncertainty bounds. It checks each split and whole ledger; it rejects missing values, invalid ordering, mismatched endpoints and insufficient output-interaction signal. A four-arm sign contrast excludes zero only when its admitted worst-case uncertainty interval excludes zero.

The schedule cancels a *common linear drift* in the factorial contrast. It does not establish independence from order carryover, nonlinear drift, correlated instrument bias or incomplete power/thermal boundaries. Differential calorimetry and synchronized true-power acquisition are still required for original-device interpretation.

## Acceptance and source disclosure

Local 2026-11-17: **86/86 passing** across the new two-store, existing load-intervention and original factorial-protocol modules. Expanded reconstructed A–H/Ω subset **287/287 passing** across ten modules. The older PWM donor suite was not included. Pinned Agda kernel, real-device metrology and connected-head CI were not run.

Full implementation: downloaded archive supplied in this conversation, containing scripts/v2_omega_split_storage_protocol.py, tests/test_v2_omega_split_storage_protocol.py, blank CSV, detailed proof note and receipt. This memo and the canonical roadmap are on the PR, but their presence must not be described as a GitHub commit of executable files until those files are present and verified by blob SHA.
