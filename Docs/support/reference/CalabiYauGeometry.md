# Calabi–Yau geometry authority

This tranche implements a reusable structural Calabi–Yau interface under
`DASHI.Geometry`.

## Modules

- `DASHI.Geometry.ComplexManifold`
  - chart coverage;
  - chart images and two-sided inverse laws;
  - point-indexed overlaps;
  - identity, inverse, and triple-overlap cocycle laws;
  - coordinate-change compatibility;
  - a compositional holomorphic-map predicate;
  - holomorphic transition maps, including inverse transitions.
- `DASHI.Geometry.Kahler`
  - an atlas-compatible tangent complex structure `J` with `J² = -id`;
  - a bilinear, symmetric, nondegenerate, positive metric;
  - Hermitian compatibility;
  - a bilinear, alternating, skew, nondegenerate two-form;
  - closedness of the Kähler form;
  - `ω(u,v) = g(Ju,v)` compatibility.
- `DASHI.Geometry.CalabiYau`
  - an integral degree-two cohomology carrier;
  - a certified first Chern class of the holomorphic tangent bundle;
  - an equality witness `c₁ = 0`;
  - a top-degree holomorphic form;
  - pointwise proof that the form cannot vanish;
  - canonical-bundle trivialization;
  - an explicit coherence relation between the Chern and volume-form
    certificates;
  - the combined `CalabiYauAuthority` package.
- `DASHI.Geometry.CalabiYauRegression`
  - a postulate-free zero-dimensional point model exercising every field and
    public eliminator.

## Definition selected

The package uses the noncompact-compatible structural definition requested by
the higher-geometry promotion lane:

1. complex-manifold charts with holomorphic transitions;
2. Kähler structure;
3. vanishing first Chern class;
4. a nowhere-vanishing holomorphic volume form.

Compactness is not silently added. Conversely, this interface does not claim
that arbitrary chart data produces a Calabi–Yau structure: a concrete producer
must inhabit every law and compatibility field.

## Proof boundary

This tranche does not derive Yau's theorem, construct a Ricci-flat metric from
a Kähler class, prove Hodge theory, or identify a physical compactification.
Those require additional analytic and geometric authority. The present result
is a proof-relevant definition and composition surface: once all requested
witnesses are supplied, the first-Chern and nowhere-vanishing conclusions are
available by projection.

The focused workflow typechecks
`DASHI/Geometry/CalabiYauRegression.agda` against the repository's pinned Agda
and standard-library setup.
