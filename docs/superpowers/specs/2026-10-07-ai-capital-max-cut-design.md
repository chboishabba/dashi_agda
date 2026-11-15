# AI-capital max-cut completion design

Date: 2026-10-07

## Intent

Complete the existing `dashi_agda` PR #1101 / `dashiTRADE` PR #1 pair without adding another representational layer. The remaining work is measurement closure and same-horizon authority: populate or explicitly retain open empirical producers, construct comparable state points, and permit capital-recovery promotion only when the existing terminal-payer and replacement/funding/rollover/obsolescence gates are satisfied.

## Non-negotiable boundaries

1. Missing empirical coordinates remain unknown, never zero.
2. Reported/proposed transactions remain non-admitted until transaction authority exists.
3. Revenue, ARR, valuation, backlog, utilisation, capability and market prices do not imply terminal cash or recovered capital.
4. Local platform telemetry does not become global market share.
5. Source receipts carry evidence and attribution only; they do not manufacture causal, legal, antitrust, bubble, insolvency or trading authority.
6. Runtime classifications remain observational. They are not trading signals.
7. Cross-time persistence requires comparable coverage and source horizon.
8. Cross-repo parity must compare the same economic object, units, admission state, coverage state and date horizon.

## Existing architecture to preserve

### `dashiTRADE`

Source observations -> admitted multiplex `CapitalGraph` -> partial coordinate bounds -> `AICapitalStatePoint` -> chronological history/persistence -> promotion readiness.

### `dashi_agda`

Attributed source carriers -> source-weighted graph / partial-coordinate owners -> observed capital state -> boundary-stable runtime mirror -> `AICapitalPerformanceResidual` -> realised capital-recovery authority only after all physical/economic obligations close.

## Max-cut implementation tranches

### A. Producer registry and provenance

Add one executable producer registry in `dashiTRADE` covering the currently named open coordinates:

- capital spread;
- inference spread;
- scarcity-rent spread;
- capability/substitutability compression;
- rollover/refinancing pressure;
- policy-backstop salience;
- market flip / volatility;
- terminal-payer coverage;
- complete revenue-vector coverage.

Each producer returns a typed observation with value-or-unknown, unit, observation horizon, source receipt(s), coverage status and admissibility. Derived values must retain dependency receipts. No producer may substitute a placeholder numeric zero for unavailable evidence.

### B. Same-horizon state construction

Extend state construction so a promotable state requires all admitted coordinates to declare compatible observation horizons. Mixed-horizon inputs may still build a partial observational state, but must carry an explicit horizon residual and remain non-promotable.

### C. Comparable temporal trajectory

Extend history diagnostics so persistence requires:

- chronological state order;
- no duplicate observation date/state key;
- comparable graph scope;
- comparable units;
- comparable producer coverage;
- compatible source horizon;
- promotion readiness at each promoted endpoint.

A transition with worse or incomparable coverage remains useful diagnostically but cannot certify a persistent regime.

### D. Cross-repo parity receipt

Add a source-written Agda owner whose fields mirror the executable runtime's exact promotion prerequisites. The owner must expose the remaining residual instead of assuming parity from matching labels. It should prove only structural implications that follow from the encoded booleans/equalities, leaving empirical truth at the source boundary.

### E. Terminal authority closure

Retain the current residual ladder:

`noTerminalPayerAuthority`
-> payer coverage
-> funding cost / capital spread
-> depreciation & replacement
-> rollover/refinancing
-> obsolescence / capability compression
-> persistence / robustness
-> realised capital recovery.

No theorem should skip a rung. A complete runtime state may feed the ladder only through a same-object parity receipt.

### F. Tests / reductions

`dashiTRADE` tests must cover at minimum:

- unknown is not zero;
- unit mismatch rejects graph aggregation;
- proposed transaction is not admitted;
- horizon mismatch blocks promotion;
- incomplete payer/revenue-vector coverage blocks promotion;
- partial HHI bounds remain valid;
- duplicate/out-of-order history rejects;
- incomparable coverage blocks persistence;
- complete synthetic fixture promotes only when every required gate is present;
- removing any one required gate causes promotion failure.

Agda source-written checks must reduce the corresponding false/true boundary cases and import through `AIEntanglementEverything2026` / `DASHI.Economics.Everything`.

## Attribution

Primary publications and platform telemetry retain primary-source status. Reuters and other reporting remain secondary carriers. Derived repo coordinates must cite the source observations from which they are computed. Unsupported global extrapolations remain forbidden.

## Definition of done

The max-cut is complete when:

1. every named open producer is either populated by a defensible source-bounded observation or represented explicitly as an unresolved producer;
2. the current state can be rebuilt deterministically from source fixtures with no implicit zeros;
3. comparable temporal states can be appended and assessed without weakening coverage requirements;
4. the executable promotion predicate and Agda residual ladder have an explicit same-object parity receipt;
5. a fully closed synthetic fixture reaches realised-capital-recovery authority while the real 2026-10-07 observation remains at its honest residual unless its missing evidence is actually supplied;
6. no additional wrapper/certificate scalar is introduced solely to make the board look green.
