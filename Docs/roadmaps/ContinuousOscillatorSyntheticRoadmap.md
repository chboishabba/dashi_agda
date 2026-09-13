# Continuous Oscillator Synthetic Roadmap

Declared surface level: `numerical diagnostic`, `receipt`, and `roadmap`.

This lane is the first executable numerical realization beneath the structural continuous-oscillator memory refinement merged in PR #896.

## Current executable slice

```text
three-frequency synthetic target
  -> N = 3 / 6 / 9 redundant oscillator conditions
  -> fixed-frequency amplitude/phase gradient learning
  -> fit/coherence/stability observables
  -> JSON + trajectory CSV + comparison CSV + Markdown receipt
  -> fail-closed Agda receipt
```

Implemented surfaces:

- `scripts/run_continuous_oscillator_synthetic.py`
- `tests/test_continuous_oscillator_synthetic.py`
- `DASHI.Cognition.PNF.ContinuousOscillatorSyntheticReceipt`
- `DASHI.Cognition.PNF.PNFIRLearningEverything`

The 3/6/9 conditions intentionally share the same three target frequencies. The larger models receive redundant oscillators rather than extra spectral support. This prevents a larger condition from winning merely because it was given additional frequencies.

## Current observables

Each `(oscillator count, seed)` run records:

- initial and final waveform MSE;
- initial and final total objective;
- loss reduction ratio;
- waveform correlation;
- global phase coherence;
- per-frequency-group phase coherence;
- gradient norm;
- last parameter-step norm;
- learned amplitudes and phases;
- unchanged frequency vector;
- convergence reason and step count.

These coordinates are intentionally not collapsed into a scalar truth or `truthiness` score.

## Default bounded result

For default seeds `7, 17, 29`, all three model-size conditions reduce waveform fit error by more than `0.999999` as a fraction of initial MSE and achieve waveform correlation extremely close to one.

The current default means are approximately:

| N | mean initial MSE | mean final MSE | mean correlation |
|---:|---:|---:|---:|
| 3 | 1.143462218688 | 3.39e-10 | 0.999999999822 |
| 6 | 0.429337767144 | 1.02255e-7 | 0.999999948433 |
| 9 | 0.367922009437 | 2.3389e-8 | 0.999999987425 |

This is not a promoted ordering. In particular, the lane does not infer `9 > 6 > 3`. N=3 has the smallest mean final fit loss in this bounded default run. N=6 and N=9 retain nontrivial hidden within-frequency phase multiplicity despite nearly identical observable target reconstruction, which is useful evidence for the hidden-state/public-observation distinction but is not yet a neuroscience result.

## Promotion boundary

The executable slice does not promote:

- neural-memory mechanism identity;
- Hebbian or Oja identity;
- Kuramoto identity;
- cognitive dissonance as oscillator energy by definition;
- empirical EEG/MEG/brain fit;
- intrinsic 3/6/9 superiority;
- quantum interpretation;
- a universal physical oscillator ontology.

`ContinuousOscillatorSyntheticReceipt` keeps each of those claims fail-closed.

## Next numerical tranches

Pareto order:

1. **Certification.** Obtain actual CI/kernel receipts for the Agda receipt and focused Python test on the PR head.
2. **Identifiability.** Add a learnable-frequency tranche only after defining frequency-separation, observation-window and gauge/degeneracy diagnostics.
3. **Update-law comparison.** Compare plain gradient phase updates with explicitly derived Hebbian/Oja/Kuramoto candidates; do not identify them by analogy.
4. **Lyapunov surface.** Test whether the declared optimization dynamics admit a monotone Lyapunov certificate, keeping fit error, phase regularization and diagnostic coherence separate.
5. **MDL/Pareto comparison.** Compare 3/6/9 by held-out reconstruction, parameter/code length, basin robustness and convergence—not by count preference.
6. **MemoryFibre adapter.** Define an explicit observation/quotient from continuous learned states into the existing public memory fibre while preserving hidden-state multiplicity.
7. **Empirical/biological adapters.** Only after the synthetic and identifiability lanes are paid, test neural data or Levin-style morphogenetic analogues with separate authority and promotion receipts.

## Validation

Focused Python inner loop:

```bash
pytest -q tests/test_continuous_oscillator_synthetic.py
python -m py_compile scripts/run_continuous_oscillator_synthetic.py
```

Formal receipt target:

```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library \
  DASHI/Cognition/PNF/ContinuousOscillatorSyntheticReceipt.agda
```

Narrow aggregate target:

```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library \
  DASHI/Cognition/PNF/PNFIRLearningEverything.agda
```

No Agda success should be claimed until one of those commands or an equivalent repository workflow actually returns green.
