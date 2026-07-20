# Concrete flat GR / quantum model tranche

This tranche advances the conditional closure ladder from Boolean/prose obligations
to small proposition-level models.  It proves that the interfaces are jointly
inhabitable and makes the forbidden shortcuts visible in the types.

It does **not** derive physical spacetime, non-flat gravity, interacting quantum
fields, gravitational mass for residues, quantum gravity, or a theory of
everything.

## 1. Flat Lorentzian producer

`DASHI.Geometry.FlatLorentzianModel` supplies:

- a four-constructor direction type `Axis4`;
- an exact `1 + 3` sign map with a unique timelike constructor;
- a balanced-ternary diagonal metric table:
  - `tri-low` for the timelike diagonal entry,
  - `tri-high` for the three spacelike diagonal entries,
  - `tri-mid` for all off-diagonal entries;
- nonzero diagonal receipts and all twelve off-diagonal-zero receipts;
- a zero Cartesian connection;
- torsion-free, flat-metric-compatible, and pointwise-zero uniqueness receipts.

This is a finite flat model and a producer for the existing conditional
`LorentzianMetricReceipt` / `LeviCivitaReceipt` interfaces.  It does not select a
metric from valuation or construct a smooth manifold.

## 2. Symbolic Einstein--Hilbert normal form

`DASHI.Physics.Closure.SymbolicEinsteinHilbertModel` makes the supplied Lovelock
conclusion executable:

- the leading symbolic bulk basis contains vacuum density and Ricci scalar;
- a boundary divergence maps to zero bulk variation;
- higher curvature remains outside the selected leading basis;
- symbolic variation maps the vacuum term to a cosmological tensor term and the
  Ricci term to an Einstein-tensor term.

The module additionally supplies an exact flat, zero-`Lambda` vacuum realization
whose Ricci and Einstein tensors are identically `tri-mid`.

This is not an internal proof of Lovelock classification or general tensor
variation.

## 3. Stress-energy and Bianchi seam

`DASHI.Physics.Closure.TypedStressEnergyMassBridge` enforces the route

```text
defect + explicit matter-action coupling
  -> action variation
  -> symmetric tensor
```

rather than exporting a coercion

```text
defect energy -> T_mu_nu
```

The concrete vacuum model supplies zero stress, symmetry, and a flat zero-source
Bianchi/conservation receipt.  Exact-once first-witness attribution is retained as
bookkeeping, but it is not promoted into stress-energy.

## 4. Mass separation

The module defines separate types for:

- `DefectEnergy`;
- `InertialMass`;
- `ActiveGravitationalMass`;
- `PassiveGravitationalMass`.

Extraction of any mass from a defect requires a `MassIdentificationWitness`
carrying a unit convention, equality receipts, an equivalence-principle witness,
and a Newtonian-limit witness.  The only canonical inhabitant is the zero-vacuum
normalization.

Consequently, ionization/MDL-style residue energy remains unidentified with
nonzero gravitational mass.

## 5. Finite quantum / flat-GR joint model

`DASHI.Physics.Closure.FiniteQuantumGRFlatModel` supplies the smallest nonempty
history model:

- one vacuum history;
- associative composition with a two-sided identity;
- an amplitude map using the existing `TriTruth` composition law;
- reflexive gauge equivalence.

It packages this with the flat Einstein-vacuum and zero-source receipts.  This
proves joint inhabitation of the interfaces, not quantization of the gravitational
field.  Unification and theory-of-everything promotion remain false.

## 6. Regression surface

`DASHI.Physics.Closure.ConcreteGRQuantumFlatRegression` re-exports compact checks
for:

- `1 + 3` signature and unique time direction;
- diagonal nondegeneracy;
- torsion freedom and flat compatibility;
- Einstein--Hilbert symbolic variation;
- flat vacuum Einstein tensor;
- zero stress and coupling-required defect sourcing;
- zero-mass normalization;
- quantum composition;
- blocked quantum-GR and ToE promotion.

## What remains genuinely open

The next nontrivial producers must address, without substituting labels for proofs:

1. a smooth or controlled continuum construction from the kernel/lift tower;
2. selection of a Lorentzian metric from valuation and admissibility data;
3. a general Levi-Civita existence/uniqueness development;
4. internal Lovelock classification or a precisely imported theorem boundary;
5. actual metric variation and boundary calculus;
6. nonzero diffeomorphism-covariant matter actions and conserved stress tensors;
7. empirical Newtonian/relativistic matching of a residue-derived source;
8. a nontrivial quantum measure with gauge, anomaly, RG, semiclassical, and
   backreaction control;
9. a novel quantitative prediction that survives independent validation.
