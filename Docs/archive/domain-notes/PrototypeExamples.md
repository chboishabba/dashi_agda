# Prototype Example States

This note supplies the first two emitted inputs for
[`scripts/prototype_runner.py`](../scripts/prototype_runner.py).
They are not data and they are not fits. They are qualitative probes for the
reduced Dashi photonuclear surrogate, generated from the canonical shift
geometry / admissibility path and a basin-preserving perturbation template.

## Files

- [`scripts/examples/near_miss_state.json`](../scripts/examples/near_miss_state.json)
- [`scripts/examples/head_on_state.json`](../scripts/examples/head_on_state.json)
- emitter:
  [`scripts/emit_shift_prototype_examples.py`](../scripts/emit_shift_prototype_examples.py)

## Intended interpretation

### Near-miss

`near_miss_state.json` is emitted from the canonical shell-1 witness used by
the shift Lorentz/RG path:

- source:
  `DASHI/Geometry/ShiftLorentzEmergenceInstance.agda::canonicalShiftStateWitness`
- basin contract:
  `DASHI/Geometry/ShiftLorentzEmergenceInstance.agda::ShiftInBasin`
- numeric representative:
  shell-1 trit seed projected into the prototype state schema

This is the prototype analogue of a clean near-miss photonuclear probe. Under
the current surrogate, it should tend to produce:

- larger `promoted_d0`
- larger `g_star`
- stronger `predicted_yield`
- better confidence than the head-on example

### Head-on

`head_on_state.json` is emitted from the same shift-path basis but with a
basin-preserving perturbation template:

- same coarse-head basin as the canonical shell-1 source
- larger spatial debris components in the defect channel
- higher MDL burden

This is the prototype analogue of a messy interior collision channel. Under the
current surrogate, it should tend to produce a weaker promoted observable and a
less favorable response than the near-miss case.

## Use

Example CLI shape:

```bash
python scripts/emit_shift_prototype_examples.py
python scripts/prototype_runner.py --state scripts/examples/near_miss_state.json
python scripts/prototype_runner.py --state scripts/examples/head_on_state.json
```

The point of these examples is explanatory inspection, not validation. They let
you compare how the prototype decomposes two channels in terms of:

- defect intensity
- MDL burden
- promoted observable strength
- inferred density proxy
- surrogate response

The emitter is the important contract here. It does not execute Agda, but it
anchors the example states to named symbols in the actual shift geometry path
instead of leaving the prototype examples as ungoverned manual fixtures.
The comparison and matrix runners now also auto-refresh those canonical
emitted example files if they are missing or stale relative to the emitter
script.

For a direct side-by-side summary:

```bash
python scripts/compare_prototype_channels.py \
  --left scripts/examples/near_miss_state.json \
  --right scripts/examples/head_on_state.json
```

That comparison should be read as a statement about the prototype's explanatory
decomposition, not as a claim that one channel is physically guaranteed to
dominate the other.

## Batch matrix

The next executable surface is a small batch matrix over the example states and
available surrogate models:

```bash
python scripts/emit_shift_prototype_examples.py
python scripts/prototype_matrix.py \
  --state scripts/examples/near_miss_state.json \
  --state scripts/examples/head_on_state.json
```

That matrix should be read as:

- channel-to-channel explanation on fixed model assumptions
- model-to-model explanation on fixed channel assumptions

It remains a surrogate explanatory tool, not a data-fit claim.
