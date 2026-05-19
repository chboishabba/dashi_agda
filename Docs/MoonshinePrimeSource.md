# Moonshine Prime Source Families

This note separates the moonshine-prime program from the photonuclear
prototype lane by naming the source families that are actually plausible inputs
to the proof program.

## Negative boundary

The following are **not** moonshine-prime source families:

- [`scripts/examples/near_miss_state.json`](../scripts/examples/near_miss_state.json)
- [`scripts/examples/head_on_state.json`](../scripts/examples/head_on_state.json)
- the photonuclear surrogate states emitted by
  [`scripts/emit_shift_prototype_examples.py`](../scripts/emit_shift_prototype_examples.py)

Those belong to the CMS/photonuclear explanatory lane, not the moonshine lane.

## Positive source-family candidates

The first plausible moonshine-native families already present in the repo are
under [`DASHI/Physics/Moonshine`](../DASHI/Physics/Moonshine):

1. **Finite twined trace families**
   - `FiniteTwinedShellTraceShift.agda`
   - `FiniteTwinedShellTraceRootSystemB4.agda`
   - `FiniteTwinedTraceComparison.agda`
   - rationale:
     these are the closest current surfaces to trace-like / twiner-like data
     rather than generic RG or photonuclear observables.

2. **Finite graded shell series families**
   - `FiniteGradedShellSeriesShift.agda`
   - `FiniteGradedShellSeriesRootSystemB4.agda`
   - rationale:
     these give graded-count style data that is at least structurally adjacent
     to generating-function questions.

3. **Twined-wave summary families**
   - `MoonshineTwinedWaveFamilySummary.agda`
   - `MoonshineTwinedWaveBundleSummary.agda`
   - `MoonshineTraceFamilySummary.agda`
   - rationale:
     these are summary/bundle surfaces where a candidate prime-support
     signature may be discoverable before any full modular lift exists.

## First executable source contract

The first executable source artifact for this lane should be a manifest over
repo-native moonshine families, not a data fit and not a modular claim.

It should record:

- source module path
- family kind (`finite_twined_trace`, `finite_graded_series`,
  `twined_wave_summary`, `comparison`)
- family label
- whether the family is shift-based, `B4`-based, or mixed
- whether the family is trace-like enough to be promoted into the observed
  moonshine-prime object lane

## Promotion rule

Before the moonshine-prime program consumes any source family, it must pass
this source gate:

1. source is moonshine-native rather than photonuclear-native,
2. source exposes trace/graded/twined structure rather than only generic
   closure summaries,
3. source can be mapped into a `MoonshinePrimeState`-like object without
   inventing new semantics.

## First adapter boundary

The first adapter built from
`DASHI/Physics/Moonshine/FiniteTwinedShellTraceShift.agda`
should be treated as an **orientation-prime adapter**, not as a full trace
extractor.

That means:

- it may legitimately read the explicit `just 31` orientation hook from the
  source family,
- it may emit a moonshine-prime state anchored on that prime and the family
  provenance,
- but it must not pretend to know the full fixed-count trace unless that data
  is extracted from a report/bundle surface later.

## First implementation seam

The first executable adapter should therefore do only the following:

1. read the explicit orientation hook from
   `FiniteTwinedShellTraceShift.agda`,
2. lift that hook into the `MoonshinePrimeState` schema,
3. mark the emitted state as `orientation_prime_only`,
4. carry enough provenance to show which family and constructor supplied the
   hook.

The first adapter must **not** infer:

- shell fixed counts,
- full twined trace coefficients,
- Monster/Ogg matches,
- modular-function semantics.

That first implementation now exists as:

- [`scripts/moonshine_prime_from_twined_trace_shift.py`](../scripts/moonshine_prime_from_twined_trace_shift.py)

and currently emits the explicit `31`-anchored state from
`shiftIdentityTwinedTrace` or `shiftNontrivialTwinedTrace` with
`basinLabel = orientation_prime_only`.

## Stronger auxiliary fields

The next strengthening step may attach **auxiliary report fields** taken
verbatim from finite-twined report/bundle surfaces, as long as they are kept
separate from the normalized moonshine-prime observable until a principled
lift exists.

Allowed examples:

- explicit verdict-slot counts,
- extra verdict counts,
- compared twiner counts,
- labeled shift twiner names,
- family-summary provenance.

These fields may travel in the emitted state under a separate auxiliary/report
payload, but they must not silently change the meaning of:

- `signature`,
- `factorVector`,
- `eigenProfile`,
- `mdlLevel`.
