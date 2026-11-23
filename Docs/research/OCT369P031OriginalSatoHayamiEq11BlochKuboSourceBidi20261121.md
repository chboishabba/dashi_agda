# OCT369 P0.31 — Original Sato/Hayami full Eq11 consumer, attribution and physical-source firewall

Date 2026-11-21. Branch agent/oct369-gravity-schumann-20261121, PR #1534.

## Original external source priority
* **Takumi Sato and Satoru Hayami**, "Quantum theory of magnetic octupole in periodic crystals and application to d-wave altermagnets", npj Quantum Materials 11, 32 (2026), DOI 10.1038/s41535-026-00865-9, https://www.nature.com/articles/s41535-026-00865-9 . Their Eqs (11)–(18), k/h quantum geometry and 18=7+5+3+3 Eq19 decomposition are the original theory. They give explicit separate degeneracy limits in Methods (Eqs 49ff). Implementing/transcribing does NOT transfer discovery.
* **Jun Ōiké, Robert Peters and Koki Shinada**, Phys Rev B 112,134412 (2025), DOI 10.1103/frq1-9xx7: independent prior thermodynamic bulk spin-octupole formulation, separate priority.
* **Kang, Hamdi, Cheung et al.**, Nature 658 (2026), DOI 10.1038/s41586-026-11172-5: source PtMn3|MgO|PtMn3 experimental octupole-driven torque/TMR, current/momentum transport. No measured static gradient lift, gravimetry or antigravity.
* Existing crystalline symmetry, velocity/Kubo, Bloch and representations are mathematical/quantum physics prior art, not originated here.

## Native DASHI ownership
P0.18 original periodic L12 24-bond Mn3/Pauli spinful H(k), P0.29 original site-vs-cell Bloch gauge/Wannier derivative/Berry/Wilson, pre-existing CoQuarterTaSeTwo experimental source constraints and numerical response modules, original crystallography direct/reciprocal donor, P0.25 27-point signed ternary address and six typed physical antigravity endpoints, and P0.28 18 vs 7 source-free Maxwell projector. No new type or duplicate Bloch/Kubo engine is needed.

## New specific consumer and replay receipt
\`scripts/check_oct369_p031_sato_hayami_eq11_source_bidi.py\`: copies the *equations*, with the SOURCE credited in the executable header, and consumes existing P0.18/P0.29 H(k). Implements both Eq12 diag and Eq13 offdiag, n≠m and n≠m≠l terms from Eqs14–18; uses analytic H velocity, acceleration/Hessian, exact occupation integrals \(T logaddexp(0,-(ε-μ)/T)\). Normalizes gμB=1 and Pauli spin matrices in model units, T=0.55 and μ=0.07; no physical SI source or measured PtMn3 input. 115/115 local program checks with script SHA \`f859a519864f8750312490d209d4d0244b92262a\`, verified as the identical uploaded GitHub blob (not a GitHub CI/Agda kernel certificate). Local execution used extracted P0.18/P0.29 original producer function subsets identical for the selected calculation; a complete repository checkout was not executed.

The full SAME Eq11 tensor agrees in physical embedded-site and periodized-Wannier cell gauges only after the expected covariant orbital-position connection: D_iHcell=(∂_i-i[X_i,.])Hcell, and the corresponding D_iD_jHcell. Per-k errors ≤4.60e-13, while naive uncorrected cell basis Eq11 differs by .0109–.0126; the correction is not a novel Berry theorem, just a necessary source/basis consistency check.

Checks over four generic k include band U1 rephasing gauge, C3 axial covariance on all three tensor indices, physical domain time reversal oddness, all 18 independent tensor components with 7+5+3+3 irreps nonzero, and positive band gaps >.02. Degenerate C3 axis points FAIL CLOSED. Coarse BZ 81/192/375 C3-symmetrized orbit samples are NOT converged; fitted bulk octupole remains completely OPEN.

## Next endpoint-first owner payments
Read/implement original published Sato/Hayami Methods degeneracy limits *without hiding divergent band terms*, plus a literal PtMn3 Wannier H(k,h) with validated crystal basis, magnetic domain/Zeeman/spin normalization and source DOI/input deck. Test full BZ mesh/gap convergence and reproduce a SOURCE original published benchmark value before associating physical units. Apply fixed film sample and Maxwell coil with a measured B second-derivative tensor, retain 18D vs 7D accessible rank, source reaction, controller energy and all P0.25 endpoint discriminators. A nonzero numerical octupole in a schematic band model is NOT new physical evidence, gravitational mass control, superconducting lift or demonstration of human levitation.


## P0.32 crystallographic connection refactor — 2026-11-22
P0.31's old inline orbital-position commutator correction was replaced by `oct369_covariant_bloch_geometry.physical_cell_jets`. The helper is the standard Bloch/Wannier connection, not a new theory. The independent P0.32 non-orthogonal crystal and general SU2 smooth frame check passed 56/56; current refactored full P0.31 source blob is `9884d70d33d892a829ea4141c9824f380e7c1e04`. The original 115-check P0.31 run belongs to historical `f859a519864f8750312490d209d4d0244b92262a`; it is not a new full-suite replay. Source attribution to original theory, crystal and existing DASHI producers unchanged.
