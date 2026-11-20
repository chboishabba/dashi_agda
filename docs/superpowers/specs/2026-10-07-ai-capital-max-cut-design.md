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


## 2026-11-21 — time-indexed geopolitical / sovereign / AI capital hyperfabric

User-originated extension: the Instagram reel proposed sovereign refinancing through an equity correction; the **yen carry intervention bridge is the user's own correlation**, not a claim attributed to the reel. Preserve supplied Gemini transcript as an adversarial narrative, not as independently verified data. Neither official denial nor temporal coincidence decides intent.

### Source ledger and clocks

- 2026-07-24: major Chinese banks cease certain individual SGE-linked precious-metal trading services (retail channel, not all institutional paper gold or all citizen gold ownership). https://www.scmp.com/business/commodities/article/3358288/major-chinese-banks-suspend-individual-trading-shanghai-gold-exchange-amid-volatility ; https://investingnews.com/china-halts-paper-gold-trading/ . The latter attributes the suppressed/"true price" interpretation to a market commentator, not verified Beijing official warning. Acquire original bank notices and actual claimed official warning separately.
- 2026-07-31: Bessent photographed note for USD5–10bn yen purchases; bank notification reportedly preceded photo by about two hours. https://www.marketscreener.com/news/bessent-s-to-do-list-buy-5-10-billion-worth-of-japanese-yen-reuters-photo-shows-ce7f50d8da8cf724 ; https://www.theguardian.com/us-news/2026/jul/31/scott-bessent-japanese-yen . Distinguish plan, signal, executed intervention, FX response and intent to affect equities.
- 2026-09-04: expected Anthropic listing before midterms per Reuters https://www.investing.com/news/stock-market-news/exclusiveanthropic-ipo-launch-shifts-toward-midoctober-sources-say-4890091 ; 09-11 Nvidia anchor investment talks https://www.investing.com/news/stock-market-news/exclusivenvidia-in-talks-to-invest-in-anthropics-mega-ipo-sources-say-4898552 .
- 2026-11-05: IPO timing doubt amid AI backlash https://www.investing.com/news/stock-market-news/exclusiveai-backlash-could-threaten-anthropic-ipo-timing-potential-investors-say-5006110 .
- 2026-11-10: prospectus https://ipo.anthropic.com/documents/us/prospectus.pdf (primary; full document extraction pending): founder voting control and aggregate USD26bn strategic private placement; recover actual final allocations, primary/secondary proceeds, lockups, counterparties and cash vs prior commitments.
- 2026-11-13: Reuters reports Huang controversies and concurrent Nvidia earnings/Anthropic IPO tests https://www.investing.com/news/stock-market-news/nvidia-results-anthropic-ipo-pose-tests-for-tumultuous-ai-trade-5028310 . User reports tech-sector narrative that leak timing served election and IPO suppression objectives; OPEN: original leaks, first publication timestamps, provenance, actor and causal evidence. Do not attribute intent or unproven wrongdoing to named people.
- 2026-11-19: IPO USD83 offer / USD111.50 opening per Reuters https://www.reuters.com/commentary/breakingviews/anthropics-2-trln-ipo-may-be-last-hurrah-2026-11-19/ ; Japanese investors sought USD9.4bn of shares https://www.reuters.com/business/finance/japanese-investors-sought-94-billion-shares-anthropic-ipo-sources-say-2026-11-19/ . Orders != allocations != settled cash != yen-funded exposure. USD100 round-number support/resistance is a behavioural hypothesis: compare crossing, order depth, volume, options strikes and placebo levels; do not presume support (could be resistance).
- Thread leads requiring original source acquisition: Bessent's Japanese fiscal/monetary pressure, executed intervention and US yield objective; China/Japan Shenzhen diplomatic snub, Taiwan dispute, oil stockpile/import recovery, gold physical clearing, critical minerals processing shares; ECB/RBA/Fed AI finance warnings, CoreWeave credit; original reel and Gemini claims. Retain distinct event, disclosure, publication, settlement, policy-effective and observation times.
- Historic network: https://offshoreleaks.icij.org/nodes/80063035 (Epstein Liquid Funding chairmanship; Bear Stearns structured finance); https://apnews.com/article/e7a5e41ba4fa3a88736cc384078c3215 (documented Trump/Epstein historic friendship). Reuse #1443 historical Epstein/Goertzel/OpenCog and EFTA00587395 proposed Humanity+ funding source lead, not settled payment. These are separate dated association/governance/funding edges, not evidence of current crash coordination or criminal responsibility.

### Hyperfabric consumer — reuse existing multiplex and temporal state owners

Define stalk X(t, scope) with fine evidence fibre (support, opposition, both, neither), source identifier, event interval, disclosure time, knowledge-as-of time, object, units, jurisdiction, actor, edge type, admissibility and uncertainty. Directed hyperedges jointly consume funding currency, leverage, collateral, counterparty, maturity and policy event; pairwise correlation does not identify the higher causal face. Preserve actual actor-dependent observation clocks and no look-ahead. Reuse existing typed hyperfabric / recursive fibre / trialectic owners where available on exact branch; no unmerged import or new ontology. Candidate 369 chart: finance=(sovereign yields, currency carry, credit); corporate=(IPO cash, equity valuation, compute commitments); physical/geopolitical=(commodity buffers, industrial bottlenecks, military/diplomatic constraints). Nine axes are a projection, not sufficient statistic; keep fine fibres, lags and opposing mechanisms.

### Rival regimes and joint tests

H0 ordinary endogenous repricing; H1 intentional tolerance; H2 deliberate controlled equity correction for sovereign refinancing; H3 selective protection or deliberate disruption of particular AI IPOs/issuers; H4 disorderly contagion. They may overlap in time/actor, not mutually exclusive labels. Bessent note pays mechanism/capability, not specific intent. US rate cuts + Japanese hikes can compress carry; yen appreciation raises unhedged dollar liabilities; Japanese repatriation/forced Treasury sales can raise yields while risk-off lowers them. Measure signed competing effects and issuance maturity/auction timing, not merely ten-year quote. Test election/leak/IPO sequences against predeclared windows, matched controls, alternative news, options/order flow and pre-trends. IPO acceleration and IPO suppression are rival hypotheses, not secretly reconciled by assumption.

China central planning / physical hedge: measure oil actual source and inventory vs imports, physical gold custody vs paper claims and retail eligibility, mineral processing vs mining share, manufacturing substitutability and energy import exposure. Do not infer inevitable Chinese victory. Japan defensive posture, counterstrike capacity, US alliance, no independent nuclear deterrent; AUKUS security partnership != BRICS economic grouping. Taiwan semiconductor and first-island-chain value plus sovereignty/legitimacy, maritime trade and domestic politics. Israel example is a counterexample to assuming economic cost minimization universally determines military decisions, not a causal equivalence or war forecast.

Household residual: 401(k) direct equity and target-date/index/indirect holdings, actual inclusion dates/free float, pension and insurer credit portfolios, unemployment, taxes and guarantees. IPO does not automatically enter every 401(k); map fund-level holdings and transfers. Compare 2008 household housing/employment/retirement losses and rescue incidence to current actual exposures; avoid claiming all losses land on retirement accounts.

### Work packets / acceptance

P0 source atlas: original notices, prospectus/final pricing, FX intervention receipts, Huang timeline, election calendar, Treasury auctions, gold warning, Shenzhen communiques, oil/critical-mineral datasets, historical association records. OPEN.
P1 temporal schema and signed dependency graph: reuse runtime CapitalGraph and AICapitalStatePoint; source-written/implemented distinction; no future information at decision time. OPEN.
P2 competing carry scenarios, round-number event study and IPO cash allocation decomposition; negative controls for both equity and Treasury responses. OPEN.
P3 physical resilience / military constraints and household incidence graph; same-object 401(k) holdings and fiscal costs. OPEN.
P4 cross-repo same-horizon parity, synthetic countermodels (same observed timing different intent; same 100 crossing different flow; same IPO price different cash recipient; same gold restriction different physical delivery; same index loss different household incidence), local Python/Agda execution per pinned tools. OPEN.
P5 update roadmap atomically with each accepted implementation, retaining open actual intent/causal/terminal-cash gates. No CI requested. This addendum is documentation and source-lead reconciliation, not executed kernel or causal verification.
