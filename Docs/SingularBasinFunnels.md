# Singular basins / hidden funnels: repo integration

Source: S. Yanchuk, S. Wieczorek, H. Jardón-Kojakhmetov, H. Alkhayuon,
**“Singular Basins in Multiscale Systems: Tunneling between Stable States,”**
*Physical Review Letters* 137, 147202 (2026), DOI 10.1103/jtkh-9lz5.

## Why this belongs in existing machinery

The reusable mathematical seam is not a new metaphorical notion of an
“attractor.”  It is a failure of basin information to survive a selected
dimensional reduction.

The existing repository already contains:

- `DASHI/Physics/Closure/Basin.agda`: eventual reachability, stable shell,
  and basin forward invariance.
- `DASHI/Cognition/CompressionAttractor.agda`: explicit compression fibres,
  fixed centres, settling certificates, and strict microstate collisions.
- `DASHI/Governance/GenericSocialAttractor.agda`: generic discrete fixed
  points and invariant regions.
- `DASHI/Biology/Cell/CellStateAttractor.agda` and protein analogues:
  attractor-relative basin membership and forward invariance.
- `DASHI/Physics/Closure/RGObservableInvariance.agda`: basin labels are one of
  the observables expected to agree across coarse/evolve schedules.
- `DASHI/Algebra/Quantum/NoGlobalAttractor.agda`: a distinct obstruction lane
  showing that not every dynamical system admits a global attractor.

The singular-basin tranche adds the **dual obstruction** to the RG/coarse
preservation story: conditions witnessing that basin membership cannot be
preserved, and in the stronger collision form cannot even factor through the
selected reduced coordinate.

## New theorem chain

`SingularBasinReductionExact.agda` defines:

1. `BasinReduction`
2. `BasinPreserving`, `BasinReflecting`, `BasinExact`
3. `BasinReductionFailure`
4. theorem `failure-refutes-preservation`
5. generic predicate factorisation through a projection
6. `ProjectionPredicateCollision`
7. theorem `collision-refutes-factorisation`
8. basin-specialised collision and non-factorisation theorem
9. local-attractor correspondence kept explicitly separate from global basin
   preservation.

This supports the formal distinction

```text
selected fixed/stable states correspond
        DOES NOT IMPLY
full basin membership is preserved by the reduction.
```

## Constructive exact witness

`SingularBasinFiniteWitnessExact.agda` contains an executable finite state
countermodel:

- `funnelState` reaches the full target and belongs to the full basin;
- its reduced image `reducedOther` is outside the reduced basin;
- `outsideState` has the same reduced image but is outside the full basin.

Therefore the module proves both:

```text
¬ BasinPreserving finiteReduction
```

and the stronger information-loss statement:

```text
¬ PredicateFactorisation project FullInBasin
```

The second theorem is the direct cross-pollination with the repository's
compression/fibre collision machinery.

## Published-model source surface

`YanchukSingularBasinSourceExact.agda` records source-facing equation owners
for the paper's slow-fast pitchfork model

```text
dx/dt  = x (mu - x^2)
dmu/dt = epsilon ((a x - b) - mu)
```

and adaptive active rotator

```text
dphi/dt = omega + mu - sin(phi)
dmu/dt  = epsilon (-mu + eta (1 - sin(phi + alpha))).
```

It deliberately does not cast the citation into an Agda proof.  Instead,
`SingularFunnelPromotion` states the exact missing promotion object: a
concrete full/reduced basin pair plus a literal `BasinReductionFailure`
witness.  Once such a witness is supplied by an analytic development or
validated selected evaluator, the generic non-preservation theorem follows
constructively.

## Next strongest implementation

1. Instantiate the pitchfork on a concrete ordered scalar carrier.
2. Reproduce the selected finite-epsilon basin witness numerically from the
   authors' public `Singular_Funnels` code/data.
3. Emit a hash/provenance-bearing witness and verify it against an independent
   evaluator.
4. Prove a certified interval/tube statement placing that witness inside the
   full basin and outside the reduced basin.
5. Add a paired state with the same reduced coordinate outside the full basin,
   upgrading reduction failure to full predicate non-factorisation for the
   selected pitchfork region.
6. Reuse the continuous-oscillator receipt style for the adaptive rotator and
   network cases.
7. Add a narrow RG bridge stating that a basin-label schedule equality would
   contradict a supplied `BasinReductionFailure`; do not modify the existing
   positive RG invariance theorem.
