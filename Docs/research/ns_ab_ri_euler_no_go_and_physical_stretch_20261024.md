# Navier–Stokes A/B decisive max-cut: Euler/Ri incompatibility and physical B witness
Date: 2026-10-24

## Provenance, distinctions, and source authority
- **OpenAI**, *Finite time blowup for the Euler equation* (released 2026-09-08), formal source `openai/NavierStokesAndEuler`, `Euler.exists_compact_smooth_euler_singularity`; already audited in DASHI `NSOpenAI2026EulerToClayFourAlternativeBidiExact.agda`. Original result belongs to OpenAI. Lean source metadata claims `sorry_count: 0`; no fresh independent kernel build here.
- **Myong-Hwan Ri**, *Global regularity for the Navier-Stokes equations with application to global solvability for the Euler equations*, arXiv:2601.15685v1 (2026-01-22), https://arxiv.org/html/2601.15685v1; Theorem 1.1, inequality (1.3), proof (3.24)–(3.30), Euler Theorem 4.2. Ri's source claim is not independently certified.
- **DASHI** owns only this compatibility audit and the new exact Fourier witness and accompanying conditional Lean proposition. Neither is an original proof of Navier–Stokes A/B.

## A: exact mathematical no-go for Ri's viscosity-*uniform* theorem
Ri's (1.3), in dimension three, claims for EVERY smooth divergence-free datum u0, all ν>0 and s≥1/2,
  sup_{t>0} ||u^ν(t)||_{H^s}² ≤ C(s) ||u0||_{H^s}²,
where C(s) is independent of ν (indeed asserted to depend only on s).

Take a smooth compactly supported datum u0 producing the unforced Euler C¹ blowup in the OpenAI released theorem. Fix any s>5/2, say s=3. Let T* be the Euler lifespan. On each [0,T] with T<T*, classical viscous-to-inviscid convergence for smooth Euler solutions with the SAME u0 implies u^ν(t)→u^Euler(t) in L² for every fixed t≤T. Boundedness of u^ν(t) in H^s independently of ν and weak compactness then give the Euler norm estimate by lower semicontinuity (one may extract a subsequence and identify its limit in L²):
  ||u^Euler(t)||_{H^s}² ≤ C(s)||u0||_{H^s}², for all 0≤t<T*.
The right side is independent of t. Because s>5/2, H^s(R³) embeds into C¹_b; hence sup_{t<T*} ||∇u^Euler(t)||_∞ < ∞. This contradicts the OpenAI Euler theorem's finite-time C¹ blowup. Thus Ri's stated estimate (1.3) cannot be true with these quantifiers, given the released Euler theorem and standard pre-blowup inviscid convergence.

**Scope:** This is a no-go for the **uniform-in-viscosity bound**, not the assertion that positive-viscosity unforced NS is globally regular for a fixed ν. The proof does not rely on the forced C/D blowup or on a false Euler→NS-blowup implication. Ri's individual frequency identities are NOT thereby falsified; do not import Ri Theorem 1.1/A3 as established. His Section 3 line (3.17) also visibly displays an unweighted gradient sum as a velocity-shell sum; inspect as a possible typographical or substantive issue rather than treating that isolated mismatch as proof of the whole theorem's failure.

**Formal code:** `chboishabba/dashi_lean4/NSEulerRiUniformViscosityNoGo.lean` proves a conditional abstract statement: if a family of viscous norms converges pointwise to the Euler norm and is uniformly bounded, the Euler norm cannot be unbounded. It does **not** formalize H^s→C¹, viscous/inviscid convergence, or import the upstream Euler theorem as a proof term. Source-written; Lean kernel unchecked this cut.

## B: exact nonzero physical spectral production, no fibre-count centering
New exact SymPy regression:
`tests/test_ns_physical_vorticity_production_exact.py`.
Normalized periodic Fourier data at p=(1,0,0), q=(0,1,2), k=p+q=(1,1,2):
  uhat(p)=(0,1,1); uhat(q)=(1,0,0); uhat(k)=i(1,-1,0),
with uhat(-m)=conj(uhat(m)), and all other amplitudes zero.
Every mode is transverse, so u is real, smooth and divergence free.

At t=0, let
  Nhat(m)=-i P_m sum_{p+q=m} (q·uhat(p)) uhat(q),
  omegahat(m)=i m×uhat(m).
Two separately evaluated EXACT finite polynomial expressions agree:
  d/dt ||u||²_nonlinear=2 Re sum_m conj(uhat(m))·Nhat(m)=0,
  d/dt ||omega||²_nonlinear=
     2 Re sum_m |m|² conj(uhat(m))·Nhat(m)=8,
  2 ∫ omega·(omega·∇u) dx [normalized average]=8.

Sign reversal of the imaginary k amplitude yields -8 for both vorticity-production formulas while nonlinear kinetic production stays zero. Inserting high-frequency zero amplitudes does not change either physical observable. This is a nonvanishing concrete bridge between the physical projected nonlinear derivative and vorticity stretching, unlike earlier shear fixtures with identically vanishing physical convection.

The same exact state has E=10, enstrophy=38, palinstrophy=198. Under amplitude u↦a u,
  nonlinear enstrophy production =8 a³,
  viscous dissipation in d/dt||omega||² at ν=1 is 396 a².
At a=50 instantaneous derivative equals +10000. Therefore *no universal fixed scalar coefficient absorbing arbitrary physical stretching only into palinstrophy* can hold for all amplitudes. This is neither a blowup construction nor an obstruction to a more delicate signed/spacetime estimate.

**Owner joins:** R236 (`NSTriadKNPhysicalParabolicCriticalRegionRoutingExact`) owns the shell classifier, R685 (`NSTriadKNR650RateKernelCommutatorEndpointRound685Exact`) owns the physical mixed-helicity commutator-minus-tangent, and R690 (`NSTriadKNR650GlobalSignedRateLiftInputLaplacianRound690Exact`) owns the signed output sum. These currently refer to a mixed-helicity R440-type field, NOT literally the u/omega enstrophy functional above. In particular the old B4 full-fibre defect is disproved. The **remaining exact theorem** is an equality or explicit remainder formula between the original selected R236 critical-production consumer and the Leray-projected u/omega production, with all selected complements compensated. This fixture is the nontrivial mandatory regression for any proposed bridge.

## Execution and acceptance
- Local Python (SymPy 1.14.0): `python -m pytest -q test_ns_physical_vorticity_production_exact.py` → 3 passed (standalone matching test).
- Source-written Lean conditional no-go and B regression committed; no Lean/Agda kernel build, no exact-PR-head pytest in this run.
- A/B claim status: A physical Fourier same-object identification and signed scale-critical A2/A3 remain open; B quantitative global signed estimate and B7 continuation remain open. C/D are released proof donors, not A/B proof closures.

**Next maximum cut:** Construct the exact physical u→ω curl/Leray spectral bridge in the actual existing R236/R685/R690 consumer and its signed compensating remainder. Separately audit Ri's earlier *valid* local-frequency estimates and the existing Bishop whole-space A2 against the Euler-compatible (necessarily viscosity-dependent or differently conditioned) continuation input. Do not create another numbered proof layer.
