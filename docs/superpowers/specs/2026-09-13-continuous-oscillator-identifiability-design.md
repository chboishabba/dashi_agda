# Continuous Oscillator Identifiability Design

## Status

Architectural design for the next numerical tranche after the fixed-frequency synthetic producer on PR #909.

This tranche asks a narrower question than mechanism identity:

> When do distinct hidden oscillator parameter states become distinguishable from finite noisy observations?

The target is the observation map

\[
\pi : \Theta \to \mathcal O,
\qquad
\Theta=(A_i,\phi_i,\omega_i),
\]

and the geometry of its fibres

\[
\pi^{-1}(y)=\{\theta : \pi(\theta)\approx y\}.
\]

The tranche does not promote a neural-memory mechanism, Hebbian/Kuramoto identity, 3/6/9 superiority, quantum interpretation, or empirical brain fit.

## Cross-pollinated constraints

### Fly/NDim anti-leakage discipline

Reuse the existing ordered pattern:

1. define the carrier and experiment grid;
2. restrict model/selection decisions to training/design coordinates;
3. freeze the identifiability rule;
4. evaluate held-out windows/seeds/noise;
5. evaluate harder holdouts separately;
6. refit inside null replicates rather than reusing the observed fit.

Held-out time windows are not automatically equivalent to held-out frequency configurations. A parameter rule that works on one spectral geometry does not establish identifiability on unseen separations.

### AdmissibleConsumerMDL discipline

Description length and Pareto ranking occur only after hard admissibility and consumer adequacy.

For this lane:

- admissible = finite parameters, gauge-normalized comparison, bounded frequency range, valid observation window, successful optimization;
- consumer adequate = held-out reconstruction below a declared error threshold and parameter-equivalence comparison computable;
- only eligible runs may enter MDL/Pareto ranking.

A smaller model cannot win merely by shorter code if it fails the held-out consumer.

## Experimental factors

The first identifiability grid varies:

- oscillator count `N in {3,6,9}`;
- observation duration;
- minimum frequency separation;
- additive observation noise;
- initialization seed;
- model redundancy within the three frequency groups;
- gauge choice / canonicalization strategy.

Frequencies become learnable in this tranche, but remain bounded to a declared interval.

## Gauge and equivalence

Raw parameter distance is not meaningful before quotienting known symmetries.

At minimum, treat these as candidate gauge freedoms:

- permutation of oscillators within the same role/group;
- phase periodicity modulo `2*pi`;
- global time-origin shift when the observation model makes it unidentifiable;
- amplitude/sign-phase equivalences when allowed by the parameterization.

Define a canonicalization or an explicit equivalence-aware distance before claiming parameter recovery.

## Primary observables

For each synthetic truth / fitted run pair record separately:

- train reconstruction error;
- held-out reconstruction error;
- frequency recovery error after matching/canonicalization;
- amplitude recovery error after matching/canonicalization;
- phase recovery error after gauge alignment;
- parameter-fibre multiplicity / number of distinct fitted states inside an observable tolerance;
- local Jacobian singular values of the observation map where tractable;
- optimization convergence diagnostics;
- basin/restart stability;
- code/parameter length coordinates for later MDL/Pareto comparison.

Do not collapse these into a scalar `truthiness` value.

## Identifiability classes

Classify a run/configuration conservatively as one of:

- `locallyIdentifiable` — nearby admissible parameter states are separated by the observation map after gauge quotient;
- `practicallyIdentifiable` — repeated fits recover the same equivalence class within declared tolerance;
- `weaklyIdentifiable` — observable reconstruction is stable but hidden parameters vary materially;
- `nonIdentifiable` — multiple inequivalent hidden states reconstruct the observation within tolerance;
- `optimizationUnresolved` — the solver has not paid enough evidence to classify identifiability.

The last class prevents optimizer failure from being misreported as mathematical non-identifiability.

## Freeze / held-out rule

All of the following must be fixed before held-out evaluation:

- parameter bounds;
- gauge/canonicalization rule;
- matching rule between recovered and true oscillators;
- reconstruction tolerance;
- parameter-recovery tolerance;
- optimizer budget;
- null definitions;
- class-assignment rule.

Held-out outcomes may not tune those thresholds retrospectively.

## Null / falsification ladder

1. **seed/restart null** — does the same observable admit materially different hidden fits?
2. **time-window holdout** — fit early/design window, evaluate later held-out samples from the same target.
3. **frequency-separation stress** — approach near-degenerate frequencies and map recovery collapse.
4. **noise ladder** — map the practical-identifiability frontier as observation noise increases.
5. **permutation/gauge null** — verify that equivalent parameter relabellings do not count as distinct recoveries.
6. **spectral-geometry transfer** — freeze the rule, then evaluate unseen frequency separations/configurations.

## 3/6/9 interpretation

The counts are experimental conditions, not an ordering.

The relevant comparison is whether increasing redundant hidden degrees of freedom changes:

- fibre multiplicity;
- practical identifiability;
- held-out reconstruction;
- basin robustness;
- convergence time;
- code length.

A result such as `N=9 has more hidden multiplicity for the same observable` would support only a structural hidden-state/public-observation distinction in the synthetic model. It would not establish a special law of nine.

## Proposed runtime surfaces

- `scripts/run_continuous_oscillator_identifiability.py`
- `tests/test_continuous_oscillator_identifiability.py`
- machine-readable JSON/CSV receipts under an output directory
- later Agda owner: `DASHI.Cognition.PNF.ContinuousOscillatorIdentifiabilityReceipt`

The implementation should reuse the existing synthetic target/model utilities where possible rather than fork a second oscillator ontology.

## Promotion boundary

Remain false until separately paid:

- `neuroscienceInterpretationPromoted`
- `memoryMechanismPromoted`
- `hebbianIdentityPromoted`
- `kuramotoIdentityPromoted`
- `cognitiveDissonanceIdentityPromoted`
- `empiricalBrainFitPromoted`
- `threeSixNineSuperiorityPromoted`
- `quantumInterpretationPromoted`
- `globalIdentifiabilityPromoted`

## Roadmap effect

After certification of #909, this tranche pays the next scientific box:

\[
\text{fixed-frequency producer}
\to
\textbf{identifiability map}
\to
\text{update-law discrimination}
\to
\text{Lyapunov}
\to
\text{MDL/Pareto}
\to
\text{MemoryFibre quotient}
\to
\text{empirical adapters}.
\]
