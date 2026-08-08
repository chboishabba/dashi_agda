# Round 28 — physical carrier, signed constituents and owner partitions

[Back to the Clay-contract overview](README.md)

Round 28 implements the exact architecture proposed by the physical-carrier and cancellation audit. It advances the proof surface only where an actual theorem can be proved without assuming a cutoff-uniform Navier–Stokes estimate.

## Exact results

### Commuting physical-carrier selector

For three commuting idempotents—Leray, Fourier reality and zero-mode centering—the composite

```text
Phys = Center o Reality o Leray
```

is idempotent. Its output is fixed by each constituent selector, and it fixes every already-admissible dependent carrier. The concrete Navier–Stokes selector instance remains open until the existing Leray idempotence/transversality cutset is connected.

### Conjugate physical-triad fibres

The involution

```text
(k,p,q) |-> (-k,-p,-q)
```

preserves resonance and the literal cutoff cube. Every triad in the output fibre over `k` receives a concrete representative in the output fibre over `-k`. Simultaneous conjugation preserves all three Plücker coordinates and squared interaction-plane area.

This supplies the finite combinatorial half of the full nonlinear Fourier-reality proof. Conjugation of the literal nonlinear coefficient and the induced sum equality remain open.

### Signed constituent tree

Every source retains its identity through

```text
source -> signed constituent -> compatible owner -> grouped majorant.
```

`LH`, `HL`, `CC` and `Com` can enter only their matching owners. `HH` can enter only `HH-good` or `HH-bad`. Kernel, tail and boundary sources have fixed owners. A nonnegative `TaxAtom` is constructed only after an owner-homogeneous signed group has been formed and bounded.

This delays positive-part collapse until the largest justified cancellation group.

### Dependent owner partition

Every Round 26 tax atom is canonically tagged by the dependent fibre over its unique owner. Erasing the tags recovers the original atom and list exactly. Both signed and taxable finite totals are preserved.

### Signed interaction fibres

A commutator interaction cell stores its shell, output mode, low translation, test symbol, multiplier and state. The exact Round 27 identity

```text
[M_m,T_l]u(k) = (m(k)-m(k-l))u(k-l)
```

is lifted through arbitrary finite structured fibres. The cutoff-uniform `TT*` or almost-orthogonality estimate remains open.

### Orbit parity and division-free Plücker defect

The four generated actions—identity, swap, simultaneous conjugation and swap-after-conjugation—have an explicit orientation character. Squared Plücker area is invariant; oriented coordinates reverse only for swap parity.

For integer scalings,

```text
|(a p) cross (b q)|^2 = (a b)^2 |p cross q|^2,
|a p|^2 = a^2 |p|^2.
```

Parallel scaled modes have exactly zero defect. No direction normalization or division is used.

### No-hidden-norm owner language

An admissible owner estimate has exactly the right-hand side

```text
eta * dissipation + data remainder + B * integral critical energy.
```

There is no constructor for an uncontrolled BKM norm, Serrin norm or target critical supremum. Finite owner estimates aggregate with the literal sum of their viscosity coefficients.

### Nine-owner absorption algebra

Once the nine physical owner estimates and a strict coefficient certificate are supplied, the signed critical balance yields

```text
Xout + (1-sum eta_i) D
  <= Xin + sum data_i + (sum B_i) integral X.
```

The physical owner estimates and `sum eta_i < 1` are not manufactured by this algebra and remain false in the authority boundary.

## Highest-alpha boundary after Round 28

The immediate route is now:

1. instantiate the concrete Leray/reality/centering selector;
2. prove conjugation of each literal nonlinear triad atom and fold it over conjugate output fibres;
3. prove the finite local-Lipschitz, Picard–Lindelöf, energy and global-flow chain;
4. derive the physical time-dependent signed shell constituent tree;
5. prove the first cutoff-uniform signed interaction-fibre estimate;
6. finish periodic strain/CZ and directional high–high taxes;
7. inhabit all nine admissible owner estimates and prove the strict total margin;
8. pass shell/Galerkin limits and complete the classical continuation chain.

## Authority boundary

Round 28 does not claim:

- a concrete physical selector instance;
- full nonlinear reality equivariance;
- finite Picard–Lindelöf or global Galerkin flow;
- a physical time-dependent shell equation;
- a cutoff-uniform `TT*` estimate;
- any physical owner tax;
- `eta_total < 1`;
- global periodic regularity;
- successful Agda or GitHub Actions validation.
