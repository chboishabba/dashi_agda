# Observer-conditioned 369/CY/KK field-and-action reduction (2026-11-18)

## Result and attribution

This is a FIRST CONCRETE field/action/observer calculation inside the existing
369 / TOE / Calabi–Yau compactification programme, **not** a new full physical
Standard Model/string unification.

Classical owners: Kaluza (1921), Klein (1926), Fourier KK mode expansion,
Laplace spectral theory on compact Riemannian manifolds, the Jacobian
smoothness criterion, hypersurface adjunction, and standard scalar action
metric variation. Geometric Fermat quintic is classical, not a DASHI
discovery.

Existing DASHI owners: `CalabiYau369CompactFibreBridge`,
`QuinticThreefoldCandidate`, `CalabiYauPhysicalProducerCutset`,
`TriadicDepthOneCharacters`, `BalancedTernaryFourierModeExact`,
`U1SU2GroupTorusExact`, `TSFVKKFiveMetricInvertibleShearExact`,
`TOEGaugeQFTGRRealizationExact`, `TOEQuantumMatterRealizationExact`,
`DASHITOETerminalMaxCutExact`, and the exact non-descent from
`KKQEDQCDVacuumConsumerBIDIExact`. No existing proof is claimed new.

User-originated hypothesis/priority: an observer's visible compact dimensions,
charges and effective interactions may vary with observational access;
explicitly derive a higher-dimensional field and carry its action/observables
through the existing 369 and TOE sectors.

Current ChatGPT-assisted bounded contribution: exact first-band action
checker, exact finite C3 action Parseval/graph-energy comparison and
continuum alias negative control, a literal C3 automorphism/fixed point
check on the existing Fermat quintic candidate, and a conditional
compact-CY scalar spectral reduction spelled out below. Exact new Agda
head **not kernel checked**. Neither check supplies a string worldsheet
or full SM.

## A. Exact 5D circle action, INCLUDING the original KK gauge field

Choose a single 5D parent metric
```
ds5² = gμν(x) dxμ dxν + R²(dθ + κ Aμ(x) dxμ)²
θ modulo 2π; R>0, κ fixed, radion R constant on this example.
```
For a 5D **real scalar** with mass μ and action
```
S5 = -1/2 ∫ d4x dθ √|g4| R
       [G5^AB ∂AΦ ∂BΦ + μ² Φ²],
```
take EXACT normalized first three modes
```
Φ(x,θ)=[u(x)+√2 v(x) cosθ+√2 w(x) sinθ]/√(2πR).
```
The metric inverse gives horizontal derivative
`Hμ=∂μ-κ Aμ∂θ`. Circle integration yields
```
∫ R dθ Φ² = u²+v²+w²
∫ R dθ (HμΦ)(HνΦ) =
 ∂μu∂νu + (∂μv-κ Aμw)(∂νv-κ Aνw)
        + (∂μw+κ Aμv)(∂νw+κ Aνv)
∫ R dθ R^-2(∂θΦ)² = (v²+w²)/R².
```
Thus the **actual same-field reduced four-dimensional action**
for the selected three-mode subspace is
```
S4 = -1/2 ∫d4x √|g4| [
 g4^μν(∂μu ∂νu + Dμv Dνv + Dμw Dνw)
 + μ² u² + (μ²+R^-2)(v²+w²) ].
Dμv=∂μv-κAμw; Dμw=∂μw+κAμv.
```
A compact-circle reparameterization acts by SO(2) rotation on the
(v,w) pair. Its charge is the n=±1 **KK momentum**, NOT a derivation
of SM electromagnetic hypercharge or SU3 colour. A full 5D real
scalar has ALL integer n, including further heavier modes. The 0,±1
subspace is closed under the quadratic/free action, but NOT under
arbitrary nonlinear self-interactions.

An observer limited to the n=0 field can measure a 4D neutral scalar
u. An observer with resolution/couplings sensitive to n=±1 can access
additional charged fields of mass² μ²+R^-2. This is the physically
meaningful sense in which observers see different *effective field
content*; the underlying spacetime dimension does NOT change between
observers. Conditional detector threshold E≳√(μ²+R^-2) is a
kinematic guide, not a universal detection theorem.

Exact source-equivalent SymPy script:
`scripts/check_string369_observer_kk_action_exact.py`.
Local equivalent execution PASS for all normalization/integration,
C3 first-band and alias tests. Exact checked-out committed blob
not run separately in this session.

### Reduced scalar stress: a bounded same-action GRQFT weld

Because `S4` was obtained by actual fibre integration of this fixed
background's **same** scalar `S5`, varying `g4^μν` at fixed R,
fixed internal mode functions and fixed A yields its 4D scalar stress
tensor. In this restricted setup differentiation under the finite
θ-integral commutes with reduction, so
`δS4/δg4^μν = ∫dθ δS5/δg4^μν`,
with compatible density and inverse-KK-metric dependence. This is a
single scalar test-sector stress identity, NOT full Einstein–YM or
quantum renormalized stress. It is not yet an Agda/Lean theorem.

## B. Direct 369/C3 sampling of that SAME field: first band and alias

At θ_j=2πj/3, j=0,1,2, take
`f_j=√(2πR)Φ(θ_j)`. Then
```
(1/3)Σ_j f_j = u,
(1/3)Σ_j f_j² = u²+v²+w²,
L_C3 = [[2,-1,-1],[-1,2,-1],[-1,-1,2]],
L_C3 f = 3(f-u·1).
```
The three-site mass/gradient matches the continuum first n=±1
band when `a²=3R²`, because `3/a²=1/R²`.

Agda source `String369ObserverFirstBandExact.agda` writes the same
three-site eigenmode basis in **rational polynomial coordinates**,
proves its Parseval and graph-gradient identities with the existing
rational ring solver, and directly reuses the original `BalancedTernaryFourierModeExact`
translation eigenlaw. Source written; **kernel unchecked**.

But `e^{2πi(n+3)j/3}=e^{2πinj/3}`. Thus C3 sampling aliases n and
n+3 even though the continuum masses `μ²+n²/R²` differ.
The first band is matched, the full high-frequency tower is NOT.
This exact non-descent is important for any continuum/physical 369
assertion, matching the original finite-path-vs-periodic-C3
operator caution.

## C. A CONCRETE Calabi–Yau threefold with a literal C3 action

Use the source-selected Fermat quintic
`X5={Σ_{i=0}^4 z_i^5=0} ⊂ CP4`.
Its coordinate cycle
`C3: (z0,z1,z2,z3,z4)→(z1,z2,z0,z3,z4)`
preserves the quintic exactly and has order three. The partials are
`∂P/∂zi=5zi^4`; over characteristic zero their simultaneous
vanishing forces all five homogeneous coordinates to zero, impossible
on projective space. So the original X5 is smooth. It is projective
and hence compact. Via standard adjunction
`K_X=O_X(d-(N+1))=O_X(5-5)`, so K_X is trivial; this is the classical
Calabi–Yau-threefold identification. A Ricci-flat Kähler metric
exists by Yau's theorem upon selecting a Kähler class, but this source
has NOT derived a concrete closed-form metric or its moduli stabilization.

**Crucial fixed-point negative control:** the actual quintic point
`[0:0:0:1:-1]` is fixed by the C3 permutation. Therefore the selected
C3 action is NOT FREE. A naive quotient can be singular/orbifold;
a smooth physical compactification needs quotient/crepant-resolution,
spin-structure and bundle-anomaly treatment where applicable.

Original DASHI physical spatial XYZ C3 and this quintic automorphism
are both explicit order-three actions, but their **intertwiner has not
been proved**. This is a positive geometric donor, not yet an action
identification or SM flavour symmetry.

Exact original-polynomial fixture:
`scripts/check_string369_fermat_quintic_c3_exact.py`, locally
source-equivalent PASS.

## D. A true 10D compact-six-dimensional scalar zero-mode reduction

Given the smooth compact quintic `X5`, choose a Riemannian metric
`h_ab` (for an actual physical CY model, eventually the selected
Ricci-flat Kähler metric), and the unwarped block target
`M10=M4×X5`, `G10=g4⊕h6`. For a free real scalar:
```
S10=-1/2∫M4×X5 √|g4|√h
       (g4^μν ∂μΦ∂νΦ+h^ab∂aΦ∂bΦ+μ²Φ²).
```
Compact Riemannian spectral theory supplies a complete L2 basis
`-Δ_X ψ_n=λ_n ψ_n`, `λ_n≥0`, with
`∫X√h ψ_n ψ_m=δ_nm` and on connected X,
`ψ_0=Vol(X)^-1/2`, `λ_0=0`.
For `Φ(x,y)=Σ_{n=0}^N φ_n(x) ψ_n(y)` and the given
fixed unwarped metric, integration by parts in X gives
```
S4=-1/2 Σ_n ∫M4 √|g4|
      [g4^μν ∂μφ_n∂νφ_n + (μ²+λ_n)φ_n²].
```
This is a **mathematical derivation of one genuine compact-CY
field/mode sector** conditional on selecting a smooth Riemannian
metric. It yields an exact normalized zero mode and a tower
`m_n²=μ²+λ_n` but NOT explicit nonzero `λ_n` for the quintic
without a specified metric and spectral solution.

If the internal metric has an isometry G, its Laplacian eigenmodes
transform in G-representations, which can organize additional mode
charges. A generic smooth CY3 need not have a continuous U1 isometry:
the S1 charged pair in section A CANNOT be silently transported to
the quintic X5 as Standard Model U1 hypercharge. The exact finite
quintic C3 automorphism may induce a discrete representation on its
mode spaces for a compatible invariant metric, but the selected
source action and actual wavefunctions must be constructed.

### Observer resolution with one underlying geometry

Define the spectral observer `P_Λ Φ=Σ_{λ_n≤Λ²} φ_n ψ_n`
at a fixed background and measurement cutoff. Then:
- a low-resolution observer gets the constant mode and a 4D EFT;
- a finer observer gains heavier modes and distinct effective
  interactions (if those modes couple to the detector);
- the complete fine state is not reconstructible from the lowest
  projection, consistent with `String369FibrePhysicalNonDescentExact`;
- what is "visible" depends on couplings, energy and measurement algebra,
  not only the number of geometric axes.

Strictly: in a QFT detector setting the observer sector is a selected
observable algebra/state and a restricted dynamical channel; an
arbitrary truncation is NOT automatically a closed interacting EFT.
Loops can influence the low-energy couplings even if high modes are
not directly excited.

## E. Actual remaining TOE field/action/observable gates

`DASHITOETerminalMaxCutExact` remains the original TOE root.
`CalabiYauPhysicalProducerCutset` ALREADY owns the full
compactification physics chain. Do not duplicate these owners.

- [x] Exact one-circle parent scalar action → 4D zero/first charged
  tower action, with normalization and gauge derivative.
- [x] Exact 3-site C3 first-band energy and explicit high-n alias
  counterexample; native finite C3 character law reused.
- [x] Fermat quintic polynomial smoothness/C3 invariance and nonfree
  fixed-point source-backed exact calculation.
- [x] Standard compact-X6 scalar Laplace spectral reduction
  mathematically specified with normalized zero mode.
- [ ] Pin a Riemannian CY metric h6, compute actual λ_n,
  select invariant C3 action and match the original 369 action
  as one representation (not just the abstract group).
- [ ] Construct actual compact CY6-real gauge connection/bundle,
  chiral Dirac zero modes, standard hypercharges, anomalies and
  mass/coupling overlap integrals, rather than assigning KK n to
  SU3 colour or SM electric charge.
- [ ] Write a selected consistent **10D string** action/worldsheet
  and quantum anomaly/BRST/GSO proof (separate RNS vs bosonic paths).
- [ ] Prove the exact SOURCE quantum g-TPS/Hamiltonian and the original
  369 Wilson observable are reductions of the selected same
  total-space field, action and physical quantum state.
- [ ] Show original QFT renormalized stress and 4D Einstein tensor
  arise from same 10D metric/source variation; fixed free scalar
  variation is only a small test-case.
- [ ] Measure/calibrate actual observer mode cutoff and coupling;
  do not infer ontological "different dimensions" from inaccessible
  high-frequency fields.
- [ ] Pinned Agda/Lean kernel acceptance; new Agda source still
  unverified in this session.

## Minimal acceptance interpretation

The work has now derived ONE honest nontrivial compactification sector
including its 4D mode masses and KK gauge coupling, plus an actual
classical Calabi–Yau base and literal C3 automorphism. It does NOT
derive the complete Standard Model or prove physical string/GRQFT
unification. Its main productive consequence is a precise observer-
indexed **observable subalgebra and mode-cutoff question** for the
existing 369/TSFV/g-TPS TOE, with explicit spectral aliasing controls.

## F. One finite QUANTUM observer-sector state/observable discriminator

The same exact free KK tower admits a low-excitation finite Fock truncation
for a *test* of observer information loss. Use two bosonic occupation
registers (one for n=0; one for n=+1), each restricted here to 0 or 1.
The two states `|0>₀⊗|0>₁` and `|0>₀⊗|1>₁` have:
- EXACTLY the same density matrix after tracing out the n=+1 register:
  `Tr_charge |ψ0><ψ0|=Tr_charge |ψ1><ψ1|=|0><0|`.
- Different expectation for the genuine internal occupation operator
  `I⊗diag(0,1)`: 0 versus 1.
- The corresponding selected KK energy differs by the n=+1 oscillator
  quantum at `ω=√(k²+μ²+R^-2)` for a specified 4D spatial momentum k.
  Ground energy must be handled by a common subtraction/regulator.

The exact matrix/partial-trace witness is now part of
`scripts/check_string369_observer_kk_action_exact.py` and passed in
source-equivalent local form. This demonstrates an actual
observer-indexed *quantum state and observable* difference for the
reduced free KK sector, not an identification with DASHI's full
source-specific g-TPS, Hamiltonian, original SM quark Hilbert spaces,
Born-rule physical measurements or interacting quantum gravity.

A measurement accessing the internal KK occupation distinguishes the
states; a base-only observer cannot. There is no change of spacetime
dimensionality, just a change of accessible observable algebra.
