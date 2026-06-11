# Avian compass bridge

## Intention

This note records the DASHI-side formalization boundary for an avian magnetic
compass bridge. The bridge treats the radical-pair compass as an observable
carrier chain:

```text
quantum radical-pair state
  -> singlet/triplet yield bias
  -> retinal chemical signal
  -> visual perturbation overlay
  -> navigation policy input
```

Agda modules:

```text
DASHI.Biology.AvianCompassSurface
DASHI.Biology.AvianCompassExamples
```

The claim is not that DASHI derives avian consciousness, subjective visual
experience, or a complete biophysical model. The claim is narrower: a
magnetic-field-sensitive quantum carrier can be represented as a perturbable
observable channel whose downstream effects remain inside retinal chemistry,
visual-state overlays, and policy-level navigation updates.

## Formal carrier map

Let `q` denote the local radical-pair carrier state in a retinal molecule such
as a cryptochrome-family receptor. The external magnetic field and local
molecular geometry enter as a perturbation context `b`. The bridge surface is:

```text
QRP(q, b) -> Yield(q, b) -> RetinalSignal -> VisualOverlay -> NavPolicy
```

where:

- `QRP` is the quantum radical-pair carrier. It contains the spin-state
  dynamics that can distinguish singlet-like and triplet-like branches under a
  magnetic perturbation.
- `Yield(q, b)` is the singlet/triplet yield bridge. It discards unobservable
  phase detail and retains only the chemically promoted yield bias available to
  downstream biology.
- `RetinalSignal` is the chemical signal surface. It represents molecular and
  neural-transduction consequences, not a direct measurement of the quantum
  state.
- `VisualOverlay` is a structured perturbation over ordinary visual input. It
  can bias orientation, contrast, directionality, or salience without replacing
  the base visual scene.
- `NavPolicy` is the behavioral policy interface that consumes the overlay
  together with other cues such as landmarks, sun compass, wind, memory, and
  proprioceptive state.

In DASHI terms, the radical-pair state is a carrier; the yield is the promoted
observable; the retinal signal is the biological adapter; the overlay is the
perception-facing state delta; and navigation is the policy consumer.

## Singlet/triplet yield bridge

The bridge should expose only yield-level quantities:

```text
Y_ST(q, b) = P_singlet(q, b) - P_triplet(q, b)
```

or an equivalent normalized yield vector:

```text
Y(q, b) = (P_singlet(q, b), P_triplet(q, b))
```

The exact Hamiltonian, hyperfine tensors, decoherence parameters, molecular
orientation distribution, and reaction-rate constants are external physics and
chemistry inputs. DASHI only requires the contract:

```text
same field-relevant context -> stable yield-class observable
changed perturbation context -> detectable yield-class delta
```

The bridge therefore avoids claiming access to microscopic wavefunction detail.
It promotes the chemically available singlet/triplet yield as the observable
surface.

## Retinal chemical signal

The retinal adapter maps yield bias into a local chemical signal:

```text
ChemSignal = f(Y(q, b), receptor-state, retinal-context)
```

This signal may be modelled as a graded activation, inhibition, noise-shift,
or contrast-bias input to visual processing. The required DASHI property is
not biochemical completeness; it is interface discipline:

- the signal is downstream of the radical-pair yield;
- it is localized to the retinal/visual processing channel;
- it is perturbable by field changes and by carrier-disrupting interventions;
- it remains distinguishable from nonvisual navigation cues.

## Visual perturbation overlay

The visual overlay is a state delta over the ordinary visual scene:

```text
V_overlay = V_base + Delta_B(ChemSignal)
```

`Delta_B` is field-sensitive but not required to be conscious, reportable, or
phenomenally transparent. Operationally it can be treated as a mask, gradient,
directional salience field, contrast modulation, or reliability-weighted cue
over the visual field.

The overlay must remain compatible with three constraints:

- it is an addition to visual processing, not a replacement for vision;
- it can be degraded, rotated, or removed by perturbing the carrier chain;
- its downstream role is policy bias rather than proof of subjective magnetic
  qualia.

## Navigation policy

The navigation consumer receives the overlay as one cue among many:

```text
a_t = Policy(V_base, V_overlay, memory, route-state, nonvisual-cues)
```

The policy-level formalization supports behavioural predictions such as:

- changed orientation distributions under controlled magnetic perturbation;
- reduced compass reliability when radical-pair chemistry is disrupted;
- cue conflict when visual landmarks and magnetic overlay disagree;
- recovery when alternate navigation cues dominate the policy state.

DASHI should represent these as observable policy deltas, not as claims that
the bird introspects a magnetic image.

## Perturbation regimes

The bridge distinguishes perturbation classes so experimental and formal claims
do not collapse into a single vague "magnetic effect":

| Regime | Carrier effect | Expected bridge-level observable |
| --- | --- | --- |
| Baseline geomagnetic field | Stable radical-pair yield bias | Reliable overlay contribution to navigation |
| Field rotation | Directional context changes | Rotated or shifted orientation preference |
| Field intensity shift | Yield sensitivity changes | Reliability or gain change in the overlay |
| Oscillating/RF disruption | Carrier coherence or reaction pathway disturbed | Degraded magnetic-cue contribution |
| Spectral/light condition change | Receptor activation context changes | Cue availability changes with visual context |
| Chemical/receptor disruption | Retinal adapter degraded | Overlay weakens or disappears |
| Cue conflict | Policy receives incompatible cues | Behaviour reflects weighting between overlay and other cues |

The formal bridge should keep these regimes separate because they stress
different parts of the chain: quantum carrier, chemical adapter, visual overlay,
or policy consumer.

## Observable vs qualia boundary

The admissible observable claims are:

- singlet/triplet yield changes under perturbation;
- retinal or neural signal changes downstream of that yield;
- visual-processing changes consistent with a magnetic overlay;
- navigation behaviour changes when the overlay is available, shifted, or
  degraded.

The inadmissible claims are:

- DASHI proves what the bird subjectively experiences;
- the overlay is necessarily a conscious magnetic image;
- quantum coherence itself is directly available to cognition;
- behavioural orientation alone proves a particular quale.

This boundary is part of the bridge. It protects the formalization from
overstating the relation between observable carrier dynamics and subjective
experience.

## Integration contract

Future Agda modules under `DASHI/Biology` should preserve this layer order:

```text
RadicalPairCarrier
SingletTripletYield
RetinalChemicalSignal
VisualPerturbationOverlay
NavigationPolicy
PerturbationRegime
ObservableQualiaBoundary
```

The modules should expose contracts rather than biochemical constants unless
an external authority surface supplies those constants. `DASHI/Everything.agda`
should import the biology modules only after they exist and typecheck.

Current targeted validation:

```text
agda -i . -l standard-library DASHI/Biology/AvianCompassSurface.agda
agda -i . -l standard-library DASHI/Biology/AvianCompassExamples.agda
agda -i . -i DCHoTT-Agda -i cubical -l standard-library DASHI/Everything.agda
```

## Ethics and no-promotion note

This bridge is for formal modelling, audit, and falsifiable-observable
separation. It is not a protocol for capturing, disrupting, disorienting, or
experimentally manipulating birds or other animals. Any empirical use requires
independent animal-welfare review, legally compliant study design, and a
non-harmful research purpose. DASHI should not promote operational guidance
for interfering with animal navigation.
