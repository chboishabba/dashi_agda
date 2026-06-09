# Retinal perturbation observation bridge

## Scope

This note records the safe join:

```text
AvianCompassSurface
  -> RetinalPerturbationSurface
  -> PerceptualObservationQuotient
  -> constrained geometry class
```

Agda module:

```text
DASHI.Biology.RetinalPerturbationObservationBridge
```

The bridge is deliberately non-promoting. It does not claim avian qualia
recovery, brain closure, fMRI validation, or a unique latent perceptual state.

## Layer Discipline

The source avian compass surface already separates the carrier chain:

```text
photon input
  -> CRY4 activation
  -> radical-pair state
  -> spin evolution
  -> singlet/triplet yield
  -> retinal chemical signal
  -> visual cue
  -> navigation policy
```

The retinal bridge starts only after a yield-level retinal signal is available.
It treats that signal as an observation channel:

```text
RetinalSignal
  -> RetinalPerturbation
  -> PerturbedVisualInput
  -> PerceptualCarrier / quotient class
  -> GeometryFamily
  -> OrientationCue
```

This keeps magnetic sensitivity as a field-sensitive observation quotient, not
as a direct image of the magnetic field and not as proof of conscious magnetic
experience.

## Formal Objects

`RetinalPerturbationSurface` introduces:

- retinal coordinates;
- a retinal perturbation carrier;
- base and perturbed visual input carriers;
- a yield-class map from `RetinalSignal`;
- a local perturbation map over retinal coordinates;
- an overlay map from base visual input and perturbation into perturbed input.

`PerceptualObservationQuotient` introduces:

- a perceptual carrier;
- a perceptual equivalence class;
- a behavior class;
- a report surface;
- a quotient from perturbed visual input;
- a geometry-class map;
- a form-constant-style geometry vocabulary;
- explicit quotient losses and a no-injectivity flag.

`RetinalPerturbationObservationBridge` joins those surfaces back to the avian
compass carriers and records:

- compass-to-quotient transport;
- constrained geometry families;
- behavior-facing orientation cue use;
- observation-only boundaries;
- `nonPromoting = true`;
- `noQualiaClaim = true`;
- `noBrainClosureClaim = true`.

## Geometry Vocabulary

The module includes a small form-constant vocabulary:

```text
directional axis
brightness gradient
lattice field
spiral field
tunnel field
cobweb field
diffuse confidence field
```

This vocabulary is not a claim that birds consciously see those exact forms.
It is a typed compression target for admissible perceptual geometry classes.
The safe statement is:

```text
retinal perturbation plus quotient constraints may narrow
the admissible geometry family.
```

The unsafe statement is:

```text
the model recovers what magnetic north feels like to the bird.
```

## Non-Promotion Boundary

The bridge explicitly blocks:

- subjective qualia promotion;
- brain-closure promotion;
- unique latent-state recovery;
- fMRI validation;
- direct magnetic vision claims.

The intended DASHI reading is:

```text
observable retinal perturbation
  -> lossy perceptual quotient
  -> constrained geometry class
  -> behavior-facing orientation cue
```

not:

```text
magnetic field
  -> recovered subjective experience
```

## Relation To Brain Lane

This module does not integrate into the brain lane as a theorem-level closure.
It only prepares a typed adapter that a later brain observation quotient can
consume:

```text
RetinalPerturbationObservationBridge
  -> future visual/connectome observation quotient
```

Any future brain integration should preserve the same many-to-one quotient
discipline:

```text
same observation may be compatible with multiple latent states.
```

Therefore joint observation may constrain latent equivalence classes better
than one quotient alone, but it still does not recover a canonical subjective
state.

## Validation Target

Current targeted validation:

```text
agda -i . -l standard-library DASHI/Biology/RetinalPerturbationObservationBridge.agda
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
```
