# MMP Dirac quantum channel × dashi_lean4 exact fermionic sources — Oct 24 2026

## Executive max-cut and real repository owners

**Lean repository inspected live:** `chboishabba/dashi_lean4`. **New dedicated draft Lean PR #85**, [`MMPDiracFockParityChannel.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/mmp-dirac-majorana-fock-channel-bidi-20261024/QuantumChannels/MMPDiracFockParityChannel.lean), [`MMPDiracChargeSuperselection.lean`](https://github.com/chboishabba/dashi_lean4/blob/research/mmp-dirac-majorana-fock-channel-bidi-20261024/QuantumChannels/MMPDiracChargeSuperselection.lean), and regression/docs. **Existing Agda draft PR #1248** owns finite Dirac/optical-loop/matched effective metric/scattering and quantum channel. Cross-repository files are **not assumed merged or kernel checked**.

Actual verified Lean source prior art:
- **#37 merged**, `CondensedMatter/MajoranaOperatorKernelExact.lean`: explicit 2×2 complex Clifford gamma, CAR, number projector; `MajoranaParityQubitExact.lean`: strict even `|00>,|11>` two-occupation logical basis; `MajoranaLogicalBraidGateExact.lean`: normalized Ising braid gates and Yang–Baxter/adjacent noncommutativity. Physical YbSb2 modes are not automatically engineered fault-tolerant qubits.
- **#61/#76 merged**, finite Born/Schwinger and quantum mereology; `RequestProject/QuantumMereologyFiniteSubsetMarginal.lean` shows each finite-subset marginal is from ONE heterogeneous global density state with exact coordinate split; `QuantumMereologyPartialTraceCoherence.lean` proves product three-factor partial-trace associativity; actual g-TPS finite HS projectors. Neither theorem selects a physical MMP operator-algebra factorization or a 4D Hadamard source.
- **#68 open**, corrected finite maximally entangled Schmidt-cut RT entropy and flat-vacuum Jacobson/Lambda=0; it is a distinct benchmark, not a proof of MMP Einstein–Maxwell–Dirac.
- **#80/#84 open**, TOE original-source and mathematical hyperfabric mirror, finite gauge/representation donors with explicitly uninhabited same-source physical closure; no rescue of unresolved global fermion QFT by matching 12/24 or C3 counts.
- Agda **#1163** already contains original source-attributed quantum teleportation vs QET vs FTL obligation taxonomy; MMP #1248 already has an effective current-normalized 1+1D Dirac S-matrix and an arbitrary selected single-particle two-angular-mode channel.

## New exact carrier / source distinction

**Single-particle mode encoding:** `|n=1>, |n=2>` has one electric charge in each basis state. A selected 2×2 transmission block `diag(t1,t2)` has mean success `(T1+T2)/2`.

**Even Fock parity encoding:** Lean #37 uses two fermionic *occupations* `|00>, |11>` (four Majorana algebraically). Its environment-no-loss branch instead has logical amplitudes `diag(1,t1t2)` for independent attenuating charged fermion modes. Its mean herald success is `(1+T1T2)/2`.

**Parity-only readout is weaker**: a double environment loss `|11>→|00>` STILL yields an even receiver, so
```
eta_even - eta_strict_no_loss = (1-T1)(1-T2)/2.
```
An ordinary parity meter at the receiver **cannot** herald no loss without further environment information. The new Lean #85 proves this real-amplitude identity, a four-term `|11>` probability normalization, and the dramatic `T1=T2=0` counterexample. Compiling the Lean proof in mathlib remains unverified; this is source-written on a draft PR.

**Stronger electromagnetic U1 selection:** the bare parity superposition `|00>+|11>` mixes **charge 0 and 2**, whereas the original single-particle angular-mode dual rail mixes two basis modes of **equal charge 1**. Without a charge-phase reference or gauge-invariant relational dressing, a charge-half-turn by `pi/2` acts as `diag(1,-1)` in the parity encoding; demanding invariance of its reduced density matrix forces charge-0/charge-2 off-diagonal coherence to vanish. The dual-rail common global phase does not destroy internal coherence. Lean #85 uses the existing actual 2×2 complex fermion matrix object to prove this selected gauge-rotation obstruction. It does NOT prohibit coherent superconducting Majorana codes with a condensate/reservoir, or all multi-subsystem gauge-invariant relational encodings.

**Original external source attribution:** Schuch–Verstraete–Cirac (2004), *Nonlocal Resources in the Presence of Superselection Rules*, PRL **92** 087904, DOI 10.1103/PhysRevLett.92.087904; Bartlett–Rudolph–Spekkens (2007), *Reference frames, superselection rules, and quantum information*, RMP **79** 555, DOI 10.1103/RevModPhys.79.555. Bennett et al (1993) own original entanglement/classical-bit quantum teleportation; Maldacena–Milekhin–Popov (2018 preprint, 2023 CQG) own four-dimensional magnetically charged-fermion negative-Casimir wormhole.

## Independent executed numerical Fock-channel verification

Companion expanded local `/mnt/data/check_mmp_fock_parity_channel_20261024.py` used two 2×2 amplitude-damping Kraus families and took their full 4×4 Fock tensor product. It checked:
- trace preservation to `≤2.5e-16` of the four Fock Kraus;
- exact even `|00>,|11>` input code, parity-even logical output and orthogonal odd-outcome erasure;
- trace preservation of the encoded 3×2 output channel to `≤1.2e-16` in the cited examples;
- Choi minimum eigenvalues numerically `≥−2.2e−20` (float roundoff), validating complete positivity;
- state-dependent `eta_single`, `eta_no-loss`, `eta_even`, and normalized maximally-entangled channel fidelities.

At **q12 effective scattering E=.20,R=240** (`T1≈.99986528, T2≈3.4463e−5`):
```
eta_single       = 0.4999498715
eta_no_loss      = 0.5000172292
eta_parity_only  = 0.5000845869
false_doubleloss = 0.0000673576786
conditional_F_e parity only = 0.5058017849
conditional_F_e true no loss = 0.5058699218
```
At **adversarial T1=.2,T2=.7**:
```
eta_single=.45, eta_no_loss=.57, eta_parity_only=.69
false_doubleloss=.12
conditional_F_e even only ≈.684178; true no-loss ≈.828216.
```
At **total physical loss** `T1=T2=0`: single-fermion transmission zero, receiver even parity accepted always, strict no-loss herald only on vacuum input half the time. Thus parity-only 'success' alone is a potentially misleading *physical observer*.

Companion `/mnt/data/check_mmp_charge_superselection_20261024.py` PASS: the unreferenced `|00>+|11>` pure logical state becomes diagonal `I/2` under discrete charge half-turn twirl (purity 1→1/2), while the equal-charge dual-rail superposition remains pure under all selected U1 rotations.

GitHub Agda committed counterparts:
```
python3 scripts/check_mmp_lean_fock_parity_channel_20261024.py
python3 scripts/check_mmp_charge_sector_coherence_20261024.py
```
The local expanded scripts were executed; GitHub exact-head runner and Lean kernel compilation **not** claimed.

## Updated P3Q phase and hard cut

1. **Default selected physical qubit candidate:** one-particle dual-rail from two genuine charged Dirac LLL/KK modes of **equal electric charge**. Need *actual source* 4D wavefunctions and asymptotic input/output current normalization; do not borrow four-Majorana parity code by basis cardinality.
2. **Optional paired-fermion/parity consumer:** separate actual two-particle Fock lift, environment loss and parity false herald; require a charge reservoir/dressing and operational preparation/readout. Source types cannot be conflated.
3. **One global state:** construct true same-universe magnetic return paths, 4D covariant Dirac Hadamard source, `<T>,<J>`, field dynamics and Einstein–Maxwell self-consistent metric; this remains primary P1/P2.
4. **Causal QI channel:** combine physical retarded 4D Dirac response with finite-N same-state partial traces (Lean #76) to derive Choi, environment trace, photon/fermion transfer and signal-front timing; no-signal-before-classical-bit in ordinary Bell LOCC.
5. **Experiment:** derive, not assume, field-driven `δα`, helicity and physical control of the state; compare static/no drive, balanced C3, broken symmetry and ordinary EM nuisance. Horned topology and 12/24 GF3 remain optional physically identified donors.

**No full globally renormalized Einstein–Maxwell–Dirac solution or experimental wormhole is established by this cross-repository mathematical advance.**
