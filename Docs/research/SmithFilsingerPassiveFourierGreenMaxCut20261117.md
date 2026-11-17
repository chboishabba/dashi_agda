# Smith/Filsinger F13 maximum cut — passive radiation and finite 2D Fourier Green
**17 November 2026 · PR #1524**  
**Mathematical target:** extend existing 4×4 oblique Maxwell spectral Green with certified passive complex radiation, exact dissipative energy work, and finite transverse inverse Fourier/Parseval.  
**Physical F13, measured F15, pinned Agda D1: remain OPEN.**

## 1. Reuse / proof chain

Reuses the repo's existing `smith_filsinger_oblique_maxwell_sympy.py` generator and its full 3×3 tilted dielectric, `smith_filsinger_tangential_maxwell_sympy.py` Cayley slab transfer, and `smith_filsinger_radiation_green_sympy.py` signed tangential sheet-source work `sheet_power_identity`. Original Balaban finite Green, KSW668 pointwise Poynting, source-indexed original port, F15 repeatable cycle cap and pinned Agda checker remain the mathematical owners; none is modified.

## 2. Passive absorbing complex radiation branch

New `scripts/smith_filsinger_passive_radiation_sympy.py` computes the strictly verified *real-frequency* outward/decaying branch

\[
q_z=\sqrt{\omega^2\mu\varepsilon-k_x^2-k_y^2},
\quad \operatorname{Re}q_z\ge0,\;
\operatorname{Im}q_z\ge0,
\]
with strict \(\omega>0,\mu>0,\operatorname{Re}\varepsilon>0,\operatorname{Im}\varepsilon\ge0\). Unproved symbolic branches, active `Im ε<0`, and spectral cutoff `q_z=0` are rejected. The same oblique Maxwell sheet-current Schur Green uses these complex admittances, without a new Green formalism.

### Exact algebraic passivity identity

For actual 4×4 Maxwell layer generator \(M\), Hermitian tangential Poynting form \(F\), positive layer thickness \(d\), and Cayley transfer

\[
T_d=(I-dM/2)^{-1}(I+dM/2),
\]
the following exact matrix identity is checked:

\[
T_d^\dagger F T_d-F
=
d\,(I-dM/2)^{-\dagger}
(M^\dagger F+FM)
(I-dM/2)^{-1}.
\]

For the passive absorbing dielectric fixture \(\varepsilon=(1+i/2)I_3\), \(\omega=2\), the *actual* Maxwell \(M\) yields

\[
M^\dagger F+FM
=\mathrm{diag}(-1,-1,0,0),
\]
therefore transfer dissipates (never produces) tangential field flux. The nonzero slab source-sheet test verifies the exact signed identity

\[
W_{\rm sheet}=\Phi_{\rm outward}+Q_{\rm absorption},
\qquad Q_{\rm absorption}>0 .
\]

The lossless tilted Hall fixture remains flux preserving; it does not become an external energy source by rotating polarization.

At zero sheet source, the Green response has zero radiated and supplied power. An evanescent lossless mode has nonzero **reactive field** with zero real time-average outward work. These are direct F15 negative controls.

**Causal caveat:** a real-frequency outgoing square-root branch and finite-Cayley passivity do **not** establish analytic continuation into the full physical upper-half complex frequency plane, a retarded temporal Green distribution, strict continuum light-cone support, or measured soil–air–ionosphere material response.

## 3. Exact finite transverse inverse Fourier and work normalization

New `scripts/smith_filsinger_periodic_fourier_green_sympy.py` reuses `oblique_sheet_green` for the four \((k_x,k_y)\in\{0,1\}^2\) modes of a two-by-two periodic, finite *mathematical* Fourier basis. It has independent forward and inverse maps, and proves by exact computation the four-character orthogonality and the spatial/modal power Parseval equality:

\[
\frac{1}{4}\sum_x \frac12\operatorname{Re}\langle E(x),J(x)\rangle
=
\sum_k \frac12\operatorname{Re}\langle\widehat E(k),\widehat J(k)\rangle .
\]

The response is assembled from genuine oblique four-component Maxwell spectral Green slices and inverted to the finite physical-position grid. The signed source/radiation/loss work sums from individual spectral modes; deliberately omitting the \(1/4\) factor **overstates source power fourfold** and is rejected.

**Limitation:** `k=0,1` are rational toy wavenumber fixtures paired with a four-character transform—not a calibrated physical Fourier grid with specified lengths or Maxwell scaling. The finite inverse is not the continuous \(\int d^2 k_\perp\) and its algebra alone does not give finite propagation speed. It does not establish original collector/ground terminal work.

## 4. Reproducible independent verification

- Previous four test owners: 51/51 PASS
- New absorbing/passive branch and exact loss controls: 10/10 PASS
- New finite 2D Fourier Green/Parseval controls: 7/7 PASS
- **All six test modules together: 68/68 PASS**, executed locally with SymPy 1.14.0, pytest 9.0.2.

Test sources:
- `scripts/test_smith_filsinger_passive_radiation_sympy.py`
- `scripts/test_smith_filsinger_periodic_fourier_green_sympy.py`

Both included in `scripts/check_smith_filsinger_dynamic_replenishment.sh` and the existing fail-closed `scripts/check_smith_filsinger_sympy_gate.py`.

Added separate reproducible workflow `.github/workflows/filsinger-sympy-exact.yml` with pinned Python 3.12, SymPy 1.14.0 and pytest 9.0.2, uploading the mathematical receipt while requiring `agda_kernel=NOT_RUN` and `D1_kernel_gate=OPEN`. This is IN ADDITION to the already existing actual Agda 2.9 workflow `.github/workflows/filsinger-agda29-acceptance.yml`; **it is NOT a substitute**.

The 68 local checks operate against the tested source-equivalent files. Full exact PR-head CI status and pinned Agda 2.9 kernel PASS were **not** observed. Existing original evidence-hash checker remains necessary before attempting any real source qualification.

## 5. Remaining max-cut gates

**F13 physical:** physical Hall/Pedersen/parallel complex conductivity fitted for original soil, atmosphere and ionosphere, realistic dispersive frequency dependence, analytic causal Green branch in upper-half-plane, full continuous 2D Fourier inversion, retarded time-domain support, spatial collector/return current including displacement current, source backaction, material/plasma active region and measured original source forcing.

**F15 measured:** a same-original independent natural-source work meter (separate from source-sheet model), calibrated signed VI at the exact receiver, all modulation/ionization/heat/radiation costs and repeated fully restored source/receiver cycles with uncertainty bounds. The finite source sheet mathematically supplies power only because a source \(J\) was explicitly stipulated, not because Sun–Earth energy was identified.

**D1 kernel:** actual pinned Agda 2.9 CI/kernel check on this PR head. SymPy mathematical verification cannot close the type-theoretic proof gate.

**Next high-alpha implementation:** build a physically parameterized complex dispersive dielectric \(\varepsilon(\omega)\) with passive Kramers–Kronig/upper-half-plane analyticity, prove a causal inverse-transform/no-prearrival support under stated source/layer geometry, and only then weld to actual calibrated original terminal observations. Use existing Agda and Green owners; no new ontology, no ESD edits, no premature TOE promotion.
