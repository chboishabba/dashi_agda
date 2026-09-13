# Continuous Oscillator Synthetic Producer Design

Date: 2026-09-13
Status: approved design
Parent architecture: merged PR #896

## Goal

Add the first executable numerical realization underneath `DASHI/Cognition/PNF/ContinuousOscillatorMemoryRefinementExact.agda` without promoting neuroscience, Hebbian identity, Kuramoto identity, cognitive-dissonance identity, quantum semantics, or any intrinsic superiority of the counts 3/6/9.

The executable slice is deliberately synthetic and falsifiable.

## Experimental conditions

Use one synthetic target waveform with exactly three fixed frequencies. Run three model sizes:

- N=3: one oscillator per target frequency;
- N=6: two oscillators per target frequency;
- N=9: three oscillators per target frequency.

All three conditions therefore have the same spectral support. The larger conditions receive redundancy, not additional frequencies.

For oscillator i in frequency group g(i):

`psi_i(t) = A_i cos(omega_g(i) t + phi_i)`

and

`Psi_N(t) = sum_i psi_i(t)`.

The target is a deterministic three-frequency waveform with fixed amplitudes and phases.

## Trainable and frozen coordinates

Frozen:

- target frequencies `omega_k`;
- sample grid and target waveform;
- deterministic seeds;
- frequency-group assignment.

Trainable:

- oscillator amplitudes `A_i`;
- oscillator phases `phi_i`.

The first tranche does not learn frequencies. Coupling is represented by a fixed regularization strength over same-frequency groups rather than by a free learned N x N coupling matrix; learned couplings are deferred until identifiability is studied.

## Objective

Use a bounded composite objective:

`F = E_fit + lambda_phase * E_phase + lambda_amp * E_amp`

where:

- `E_fit` is mean squared waveform error;
- `E_phase` is same-frequency phase disagreement, using `1 - cos(phi_i - phi_j)` within each frequency group;
- `E_amp` is a small L2 amplitude regularizer.

Do not put the earlier Laplacian/curvature construction into the optimizer. Curvature, if later used, is a diagnostic rather than automatically a synthesis-producing term.

Use explicit gradient descent on amplitudes and phases. This demonstrates gradient learning only. It does not establish equivalence with Hebbian, Oja, or Kuramoto learning.

## Readouts

Record separately, without scalarizing them into a truth score:

- fit loss;
- total objective;
- loss reduction ratio;
- global phase coherence r;
- per-frequency-group coherence r_k;
- waveform correlation;
- gradient norm;
- parameter-step norm;
- convergence status/reason;
- initial and final amplitudes/phases;
- fixed frequencies;
- seed, steps, sample count and hyperparameters.

Per-group coherence is primary because distinct target frequencies have no reason to share absolute phase.

## Required artifacts

Producer:

- `scripts/run_continuous_oscillator_synthetic.py`

Focused tests:

- `tests/test_continuous_oscillator_synthetic.py`

Machine-readable artifacts under a caller-provided output directory:

- `continuous_oscillator_synthetic.json`
- `continuous_oscillator_trajectories.csv`
- `continuous_oscillator_comparison.csv`
- `continuous_oscillator_synthetic.md`

Formal receipt:

- `DASHI/Cognition/PNF/ContinuousOscillatorSyntheticReceipt.agda`

Narrow discoverability wiring:

- `DASHI/Cognition/PNF/PNFIRLearningEverything.agda`
- `Docs/roadmaps/SimulatorRoadmap.md`

## Promotion boundaries

Every numerical receipt must explicitly keep these false:

- `neuroscience_interpretation_promoted`
- `memory_mechanism_promoted`
- `hebbian_identity_promoted`
- `kuramoto_identity_promoted`
- `cognitive_dissonance_identity_promoted`
- `empirical_brain_fit_promoted`
- `three_six_nine_superiority_promoted`
- `quantum_interpretation_promoted`

The synthetic producer may establish deterministic execution, loss/coherence observables, fixed-frequency invariance, and bounded convergence for its declared runs only.

## Success criteria

The tranche is successful if:

1. a fixed seed reproduces byte-equivalent numerical summary values;
2. N=3,6,9 all execute against the same three-frequency target support;
3. frequencies are unchanged by training;
4. fit loss decreases for all declared default conditions;
5. artifacts expose the full promotion boundary;
6. tests make no claim that 9 must outperform 6 or 3;
7. the Agda receipt records the execution surface without turning numerical success into neuroscience or 3/6/9 authority.

## Deferred

- learned frequencies;
- learned dense coupling matrices;
- identifiability theorem;
- Hebbian/Oja/Kuramoto reduction theorem;
- EEG/MEG or other empirical neural fitting;
- MemoryFibre empirical adapter;
- Levin/morphogenesis numerical realization;
- CRT projectors on the continuous carrier;
- MDL/Lyapunov promotion beyond the diagnostics emitted here.
