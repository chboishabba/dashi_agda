# Conditional GR / quantum closure ladder

## Purpose

This tranche advances the valuation-vacuum geometry seam without converting
physics-language correspondences into unconditional theorems.

The key change is from boolean roadmap labels to proposition-indexed receipts.
Each requested promotion now has an explicit producer interface and a theorem
that composes supplied witnesses.  The repository still does not internally
prove the differential-geometric, variational, quantum, or empirical premises.

## Cross-pollination

The implementation combines four existing ideas:

1. `DASHI.Geometry.AdmissibilityJetSpec`
   supplies the quotient-first, local finite-jet rows for metric, connection,
   spinor, gauge, and bitensor carriers.
2. `DASHI.Physics.Closure.ValuationVacuumEinsteinBoundary`
   supplies saturation, residue, valuation, and non-promotion boundaries.
3. `DASHI.Physics.Closure.FirstWitnessVacuumBridge`
   supplies the Euler/PDA lesson: a unique first witness permits irreversible,
   exact-once defect attribution and schedule-invariant final discharge.
4. The repository's established fail-closed discipline keeps a conditional
   receipt separate from a derivation of its premises.

The first-witness result is useful for avoiding duplicate source accounting.
It is not itself a stress-energy tensor, a metric, or an equivalence-principle
proof.

## Closure chain

### 1. Lorentzian metric

`DASHI.Geometry.LorentzianLeviCivitaConditional` requires explicit witnesses
for:

- a smooth four-dimensional base;
- a supplied nondegenerate metric;
- one timelike and three spacelike directions.

It then packages a `LorentzianMetricReceipt`.  The canonical example explicitly
records that the valuation carrier does **not** yet select this metric.

### 2. Levi-Civita connection

The same module requires:

- a supplied connection;
- torsion freedom;
- metric compatibility;
- uniqueness among torsion-free metric-compatible connections.

These premises compose into a `LeviCivitaReceipt`.  This is the exact theorem
interface needed for a later internal existence/uniqueness development.

### 3. Einstein-Hilbert basis and variation

`DASHI.Physics.Closure.EinsteinHilbertVariationConditional` requires the full
metric-Lovelock hypothesis row:

- diffeomorphism invariance;
- locality;
- metric-only dynamical geometry;
- four dimensions;
- at most second metric derivatives;
- boundary-term separation;
- a supplied Lovelock classification.

Only under those premises is the leading basis recorded as the constant and
Ricci-scalar terms.  A second witness supplies the metric variation, boundary
control, Einstein tensor, cosmological term, and normalization constants.

The module explicitly rejects the claim that valuation alone forces the
Einstein-Hilbert action.

### 4. Stress-energy and Bianchi compatibility

`DASHI.Physics.Closure.StressEnergyBianchiConditional` separates three layers:

1. exact-once defect attribution from the unique-first-witness lane;
2. a symmetric stress-energy tensor from metric variation of a
   diffeomorphism-invariant matter action;
3. covariant conservation from contracted Bianchi, matter equations of motion,
   and a Noether identity.

This prevents the common invalid step

```text
defect energy => stress-energy tensor
```

without an explicit coupling and variation theorem.

The mass boundary separately requires definitions of inertial, active, and
passive gravitational mass, an equivalence-principle bridge, and Newtonian-limit
matching.  Ionization-style or MDL defect energy remains un-identified with
mass.

### 5. Quantum / GR compatibility

`DASHI.Physics.Closure.QuantumGRActionCompatibilityBoundary` records the
strongest presently justified shared seam: classical geometry and a quantum
history/state construction may consume one admissible action carrier.

A conditional compatibility receipt requires:

- state or history space;
- gauge-redundancy control;
- a measure or amplitude rule;
- composition;
- positivity or unitarity;
- anomaly freedom;
- renormalization;
- a controlled semiclassical limit recovering the Einstein equation;
- controlled matter backreaction.

A shared action vocabulary is therefore weaker than quantum gravity.

## Remaining promotion gates

Quantum-GR unification remains blocked until the repository derives or imports
checked proofs for at least:

- a common kernel tower yielding both geometric and quantum carriers;
- the observed gauge group and matter representations;
- anomaly cancellation;
- a controlled UV completion or explicitly bounded effective regime;
- recovery of GR, QFT, and known low-energy limits;
- empirical constants or a principled account of their free status;
- a novel quantitative prediction that survives experiment.

Theory-of-everything promotion additionally requires demonstrating coverage of
all intended interaction and matter sectors, not merely a compatible interface.

## Regression

`DASHI.Physics.Closure.ConditionalGRQuantumClosureRegression` confirms:

- the conditional Lorentzian, Levi-Civita, Einstein-Hilbert, conserved-source,
  and quantum/GR compatibility receipts are constructible;
- valuation-only Einstein-Hilbert selection remains false;
- residue energy equals mass remains false;
- quantum-GR unification remains false;
- theory-of-everything promotion remains false.
