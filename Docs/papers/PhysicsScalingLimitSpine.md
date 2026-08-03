# Physics Scaling and Limit Spine

## Claim discipline

The shared mathematical thesis is:

```text
unification
  = shared quantity semantics
  + shared observable semantics
  + exact or controlled theory translations
  + explicit promotion boundaries.
```

A theory-to-theory relation is not established merely because two constructions
use the same finite carrier. Exact recovery requires a commuting square. An
effective theory requires a controlled residual. An asymptotic limit requires a
vanishing-residual theorem.

## Shared mechanical dimensions

`DASHI/Physics/Units/MechanicalDimensionExact.agda` introduces one integer
`M-L-T` dimension algebra and dimension-indexed quantities. It proves the exact
identities used downstream, including

```text
[velocity] [time] = [length]
[velocity gradient] [time] = 1
[power] [time] = [energy]
[Newtonian potential] = [speed squared]
[partial_t u] = [(u . grad)u] = [nu Delta u] = [acceleration].
```

The existing nominal finite wrappers in
`DASHI/Physics/QuantumVacuum/PhysicalQuantities.agda` are retained. The bridge
assigns them dimensions without identifying semantic types such as Energy and
Work. It also preserves the existing warning that `averagePower` is a finite
accounting proxy, not a proved quotient law.

Primary dimensional-analysis provenance:

- Edgar Buckingham, *On Physically Similar Systems; Illustrations of the Use of
  Dimensional Equations*, DOI `10.1103/PhysRev.4.345`.

## Navier--Stokes and Luo normalization

`PhysicalNormalizationExact.agda` keeps the general `(L,U)` normalization and
proves

```text
(U / L) (L / U) = 1.
```

`NSTriadKNNavierStokesNormalizationTransportExact.agda` sits between the generic
scale algebra and the source-specific Luo theorem. It proves the exact
mechanical dimensions of the time derivative, advection, pressure-gradient,
viscous-Laplacian and integrated-dissipation terms. It then supplies one
proof-relevant transport owner for:

1. the physical-to-normalized Navier--Stokes equation;
2. the physical and normalized energy identities;
3. the parabolic terminal window;
4. the retained inverse-Reynolds coefficient.

The energy and terminal-window diagrams are represented as exact commuting
squares. Their concrete inhabitants must come from the official continuum
solution construction; they are not replaced by Boolean normalization flags.

`NSTriadKNLuoScalingExact.agda` then transports the exact scale cancellation to
the official periodic Luo carrier. Therefore the normalized and physical
versions of

```text
integral ||grad u_{<=p}||_infinity dt
```

agree exactly once the scale interpretation is supplied. Luo's `nu=1`
convention is represented as the special viscous selection `U = nu/L`, or
`Re=1`; it is not built into the general dimension algebra.

The dimension and scale-cancellation theorems are machine checked. The concrete
continuum equation/energy/window transport is conditional, and Luo's
continuation theorem remains `standardImported`.

Primary sources:

- Jean Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, DOI
  `10.1007/BF02547354`;
- Xiaoyutao Luo, *A Beale--Kato--Majda Criterion with Optimal Frequency and
  Temporal Localization*, DOI `10.1007/s00021-019-0411-z`.

## Weak-field general relativity

`GRWeakFieldDimensionExact.agda` reuses the repository's finite flat
mostly-plus `(-,+,+,+)` carrier and proves that the Newtonian potential and
`c^2` have the same mechanical dimension. Hence `Phi/c^2` is a legitimate
dimensionless metric perturbation.

The Newtonian Poisson limit is not collapsed into one unnamed hypothesis. Its
authority requires separate inhabitants for:

1. weak metric perturbation;
2. trace-reversed linearization;
3. harmonic gauge;
4. static-field reduction;
5. nonrelativistic `00` source identification.

The module does not prove Schwarzschild--Birkhoff recovery or non-flat Ricci
convergence.

Primary sources:

- Albert Einstein, *Die Grundlage der allgemeinen Relativitaetstheorie*, DOI
  `10.1002/andp.19163540702`;
- Juergen Ehlers, *On the Newtonian Limit of Einstein's Theory of Gravitation*,
  DOI `10.1007/s10714-019-2624-0`.

## Yang--Mills mass scale

`BalabanClayT5MassScaleDimensionExact.agda` reuses the existing exact T5
transport. It clarifies that

```text
dimensionless gap * inverse lattice spacing
```

first has inverse-length dimension. An SI mass additionally requires an
explicit `hbar/c` conversion or a selected natural-unit convention.

A renormalization scheme and its matching function are explicit. Agreement
between two schemes after conversion is a separate obligation and is not
inferred from dimensional correctness.

Asymptotic-freedom provenance:

- David J. Gross and Frank Wilczek, *Ultraviolet Behavior of Non-Abelian Gauge
  Theories*, DOI `10.1103/PhysRevLett.30.1343`;
- H. David Politzer, *Reliable Perturbative Results for Strong Interactions?*,
  DOI `10.1103/PhysRevLett.30.1346`.

## Exact, residual and asymptotic squares

`PhysicsLimitCommutingSquare.agda` supplies:

- exact path independence;
- residual identities with explicit control predicates;
- scale-indexed residual families with a vanishing theorem.

`QuantumClassicalGravityBoundaryIntegration.agda` attaches these notions to the
existing full-physics and strict GR/quantum authority surfaces. The new shared
foundations do not synthesize the continuum authority cutset, and the terminal
quantum-gravity and theory-of-everything flags remain false.

## CMS below-Z empirical contact

The strongest currently inhabited empirical statement is deliberately bounded:

> DASHI has a bounded empirical contact with CMS-SMP-20-003 t43. The frozen
> t43/t44 covariance comparison for the 50--76 / 76--106 GeV Drell--Yan ratio
> gives chi2/dof = 2.1565191176 and mean prediction/data = 0.9941233097 at
> commit `3205d746639568762c9e97adf4a3672c356bd491`.

The Agda module verifies the typed receipt, source binding, exact recorded
values, hashes, scope and non-promotion boundary. The external floating-point
covariance computation is byte-replayable but is not recomputed by the Agda
kernel.

The stronger early statement is retained as a formal target rather than erased.
`StrongEarlyClaimAuthority` requires both:

- one common-spine authority recovering spacetime geometry, spinor fields,
  gauge representation, wave dynamics and stress-energy; and
- a parameter-inventory authority proving the prediction was frozen before the
  CMS comparison and that neither t43 nor t44 was used for calibration.

No inhabitant is currently constructed, so the repository cannot yet promote
“zero fitted parameters” or infer whole-spine validation from this one contact.

Publication provenance:

- CMS Collaboration, *Measurement of the Mass Dependence of the Transverse
  Momentum of Lepton Pairs in Drell--Yan Production in Proton--Proton
  Collisions at sqrt(s) = 13 TeV*, DOI
  `10.1140/epjc/s10052-023-11631-7`.

## Validation

Run:

```bash
bash scripts/check_physics_scaling_limit_spine.sh
```

The focused check rejects explicit postulate blocks, verifies provenance and
claim-boundary markers, and type-checks every owner plus the aggregate import
surface with the repository's Nix-pinned Agda 2.9 runner.
