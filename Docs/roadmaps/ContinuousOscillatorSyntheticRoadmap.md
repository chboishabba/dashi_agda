# Continuous Oscillator / Recursive Scale Roadmap

Declared surface level: `structural refinement`, `synthetic numerical diagnostics`, `formal receipts`, and `roadmap`.

## Parent chain

This programme follows its parent rather than treating each tranche as a new ontology:

```text
existing MemoryFibre / phase / learning / decision machinery
  -> merged PR #896: continuous hidden oscillator refinement
       + recursive level-indexed scale transition
  -> PR #909: fixed-frequency synthetic 3/6/9 producer
  -> PR #909 continuation: learnable-frequency query-indexed identifiability
  -> update-law discrimination
  -> Lyapunov / stability analysis
  -> eligible-only MDL / Pareto comparison
  -> explicit continuous-state -> MemoryFibre observation/quotient
  -> empirical neural / Levin adapters
```

Certification is orthogonal proof debt: implementation/source integration may advance while an Agda runner is unavailable, but no kernel theorem status is promoted without an actual execution receipt.

## Thread invariants retained from the structural parent

The programme continues to enforce the decisions made before the first numerical producer:

- there is no universal physical `F`; scale transition is level/domain indexed;
- environment and history remain explicit inputs to situated lower-scale dynamics;
- persistence is broader than fixed-point/local-minimum attraction and may include invariant sets, metastable classes, phase-locked sets, limit cycles modulo gauge, and other stable equivalence classes;
- persistent lower-scale structure does not become next-scale semantic identity without an explicit realisation witness;
- `MemoryFibre` remains the public semantic memory carrier;
- continuous phase is not definitionally finite `Phase3` and does not create a Hilbert/quantum interpretation;
- objective value, learning/update rule, and observed cognitive/behavioural measurement remain distinct;
- oscillator mismatch is not cognitive dissonance by definition;
- target/reference states are present-time constraints and do not imply backwards-in-time causation;
- the oscillator objective does not merge the repo's distinct energy carriers.

## Fixed-frequency executable tranche

PR #909 first established a deliberately bounded falsifiable producer:

```text
three-frequency synthetic target
  -> N = 3 / 6 / 9 redundant oscillator conditions
  -> fixed-frequency amplitude/phase gradient learning
  -> fit/coherence/stability observables
  -> JSON + trajectory CSV + comparison CSV + Markdown receipt
  -> fail-closed Agda receipt
```

All three conditions share the same target spectral support. Larger conditions receive redundant oscillators, not additional target frequencies. Default seeds `7,17,29` produced near-perfect waveform reconstruction in all three conditions while larger redundant models retained hidden phase multiplicity. That observation motivates identifiability work; it does not establish `9 > 6 > 3`, neuroscience, or mechanism identity.

## Query-indexed identifiability tranche

The next runtime is now explicit:

- `scripts/run_continuous_oscillator_identifiability.py`
- `tests/test_continuous_oscillator_identifiability.py`
- `DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityReceipt`
- `DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityRegression`

Frequencies become learnable inside declared bounds. The design freezes optimizer budget, frequency bounds, train/held-out split, gauge/matching policy, observable tolerance, and parameter tolerance before held-out evaluation.

Identifiability is query-relative. Reuse `DASHI.Core.QueryIndexedProjectionAdequacyExact`:

```text
hidden state Theta --pi--> observation O
        |                  |
        Q                  Qbar
        v                  v
      answer  <------------
```

For a query `Q`, exact identifiability means `Q` factors through the observation projection. The query family is kept separate:

- waveform reconstruction;
- frequency recovery;
- amplitude recovery;
- phase recovery after declared gauge normalization;
- complete canonical hidden-state recovery.

A numerical near-collision is only a diagnostic approximation to the exact fibre-collision theorem shape. It is not an Agda `QueryAdequacyDefect` unless an exact finite witness is separately constructed.

## Cross-pollinated experiment discipline

From Fly/NDim and Grokking:

```text
define carrier/rule
  -> fit/select on training/design coordinates
  -> freeze
  -> held-out time evaluation
  -> harder held-out spectral geometry
  -> nulls/refits
```

Held-out time is not equivalent to unseen spectral geometry. Held-out outcomes may not tune matching, tolerances, optimizer budget, or null definitions. Optimizer failure is `optimizationUnresolved`, not mathematical non-identifiability.

From admissible-consumer MDL/Pareto:

```text
admissible
  + consumer adequate
  -> eligible
  -> only then compare description length / Pareto cost
```

Thus neither fewer parameters nor richer hidden multiplicity wins the 3/6/9 comparison by itself.

## Attribution / snowball / external identity discipline

All scientific sources used by this programme retain the repository `AttributedSourceCore` coordinates and `SnowballAttributionProvenanceInvariantExact` role invariants: author, title, publication, DOI state, canonical URL, source kind, formalisation relationship, visibility, and proof/authority non-promotion.

The identifiability adapter currently retains David Blackwell, *Equivalent Comparisons of Experiments* (1953), DOI `10.1214/aoms/1177729032`, only as an information-comparison precedent inherited through the query-indexed projection-adequacy parent. Blackwell does not author the DASHI oscillator construction and citation does not prove numerical identifiability.

OEIS, Wikidata QIDs, Dewey coordinates, and other external identifiers are optional identity/navigation coordinates, not decoration. Add them only where the same object or a role-relevant external concept is actually paid. In particular, the digits `3/6/9` do not create semantic identity across Base369, oscillator count, Tesla folklore, physics, cognition, or any other domain.

## Remaining Pareto frontier

1. **Execute/certify the identifiability runtime.** Obtain actual pytest/Python receipts and map near-collision/recovery behaviour across seeds before promoting any numerical observation.
2. **Finish identifiability stress/nulls.** Add frequency-separation ladder, noise ladder, restart multiplicity, gauge null, and unseen spectral-geometry transfer with refitting where required.
3. **Update-law discrimination.** Compare the current gradient rule with separately derived Hebbian, Oja, and Kuramoto candidates. Analogy is not identity; each candidate needs its own source and derivation chain.
4. **Lyapunov/stability.** Ask whether each declared update admits a monotone Lyapunov quantity; keep fit error, regularisation, phase coherence, and semantic/empirical adequacy distinct.
5. **Eligible-only MDL/Pareto.** Compare 3/6/9 using held-out reconstruction, query adequacy, code/parameter length, basin robustness, convergence and null stability only after eligibility gates pass.
6. **MemoryFibre quotient.** Build the explicit observation/quotient from continuous learned states into the existing public memory fibre, preserving remembered-event identity while retaining hidden multiplicity.
7. **Recursive-scale realisation.** Only with an explicit `RealisesNext` witness may a persistent lower-scale oscillator class become a next-scale effective object.
8. **CRT continuous-carrier lane.** Separately investigate CRT/projector structure on a genuine continuous module/Hilbert-like carrier; do not smuggle finite Base369/Phase3 arithmetic into the oscillator carrier by shared numerals.
9. **Empirical adapters.** EEG/MEG/neural data and Levin-style morphogenetic analogues remain downstream and require separate source, authority, same-object, measurement, and promotion receipts.

## Promotion boundary

Remain fail-closed until separately paid:

- neural-memory mechanism identity;
- Hebbian/Oja/Kuramoto identity;
- cognitive-dissonance identity;
- empirical EEG/MEG/brain fit;
- intrinsic 3/6/9 superiority;
- quantum interpretation;
- universal physical oscillator ontology;
- global identifiability;
- Levin-specific realisation;
- one physical energy governing all scales.

## Verification wall

Focused Python targets:

```bash
pytest -q tests/test_continuous_oscillator_synthetic.py tests/test_continuous_oscillator_identifiability.py
python -m py_compile scripts/run_continuous_oscillator_synthetic.py scripts/run_continuous_oscillator_identifiability.py
```

Focused formal targets:

```bash
agda -i . -i DCHoTT-Agda -i cubical -l standard-library \
  DASHI/Cognition/PNF/ContinuousOscillatorIdentifiabilityRegression.agda

agda -i . -i DCHoTT-Agda -i cubical -l standard-library \
  DASHI/Cognition/PNF/PNFIRLearningEverything.agda
```

No Python or Agda GREEN is claimed for a new head until the corresponding command/workflow is actually observed to pass.
