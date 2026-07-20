# Tech/Systemic Stress Scenario Boundary

This tranche formalises the market/news scenario architecture discussed around
CA-derived BAD windows, Greece-style news alignment, AI/technology concentration,
funding transmission, and regime-conditioned capital posture.

## Modules

- `DASHI.Promotion.TechSystemicStressScenarioBoundary`
- `DASHI.Promotion.TechSystemicStressScenarioRegression`

The boundary reuses:

- `DASHI.Foundations.SSPTritCarrier` for the canonical signed
  `{-1, 0, +1}` carrier;
- `DASHI.Promotion.PNFSpectralTradingSignalBoundary` for receipt-backed market
  information surfaces and incoming evidence braids; and
- `DASHI.Promotion.PNFSpectralEmpiricalBasinValidation` for field windows,
  good/bad/tail basin vocabulary, and fail-closed empirical validation.

## Layer separation

The formal machine keeps four layers distinct:

```text
observation -> structural classification -> capital posture -> execution family
```

The signed structural regime means:

- `-1`: adverse/incoherent structural condition;
- `0`: unresolved/ambiguous structural condition;
- `+1`: favorable/coherent structural condition.

These values do **not** mean price down/flat/up. In particular, the adverse
state is not definitionally a short signal.

The corresponding posture map is:

- adverse -> defensive posture;
- unresolved -> observational posture;
- favorable -> opportunity posture.

Execution families remain separately bounded. The defensive posture may name
flat, carry-only, bounded hedge, or convexity-candidate families, but arbitrary
sign inversion and future-return-conditioned execution are explicitly false.

## Stress axes

The typed axis registry includes:

- liquidity;
- funding;
- correlation;
- narrative instability;
- execution churn;
- Treasury functioning;
- credit transmission;
- technology concentration;
- capex revision;
- secondary hardware markets; and
- power/cooling constraints.

This permits a scenario to be described by observable transmission axes rather
than by a deterministic story such as “one stock falls 30%, therefore a
sovereign crisis follows in three months.”

## Phase ladder

The phase carrier distinguishes:

1. latent fragility;
2. trigger proximity;
3. active dysfunction;
4. stabilization; and
5. unresolved phase.

Every canonical phase assessment remains receipt-pending, non-predictive, and
without sovereign-crisis authority.

## Adverse-onset windows

`AdverseInterarrivalWindow` records the interval between adverse-regime onsets.
This captures the proposed “time between bad days” geometry while allowing
neutral or favorable substructure inside the interval. The record carries
severity, persistence, event-count, timestamp, and replay-receipt digests.

## News and scenario attribution

`ScenarioAttributionCandidate` distinguishes generic risk stress,
sovereign/funding stress, technology-duration stress, AI-capex stress,
Treasury-liquidity stress, mixed stress, and unattributed stress.

Two canonical fixtures are included:

- a Greece-style sovereign/funding stress fixture, preserving the remembered
  mid-July-2015 alignment only as a post-hoc replay fixture; and
- an AI-capex/technology-duration stress candidate requiring technology
  concentration, capex, hardware resale, power/cooling, funding, and credit
  transmission receipts.

News is corroboration rather than the detector. Missing provider coverage is
not evidence of no event, and a headline match is not causal proof.

## Promotion boundary

The tranche does not promote:

- market prediction;
- financial advice;
- production execution;
- deterministic crisis countdowns;
- causal attribution from headline alignment;
- arbitrary shorting from an adverse state; or
- empirical adequacy without replay and holdout receipts.

The regression module checks the signed-regime meanings, posture map, layer
separation, and the canonical non-promotion flags.
