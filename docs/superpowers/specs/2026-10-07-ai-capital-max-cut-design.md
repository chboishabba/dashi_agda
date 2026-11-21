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


### 2026-11-21 — existing-owner audit, supersedes blanket P0–P4 OPEN

Source inspected (not kernel verified): #1101 AICapitalObservedStateTimeSeries2026Exact already has ObservedCapitalStatePoint, CapitalStateTransition, PersistentCapitalTrajectory; current point explicitly nonpromotable. AICapitalOutcomeCompatibility20261016Exact already has OutcomeFit with supported/contrary/unresolved coordinates and forbids terminal selection; extend rival hypotheses without claiming existing scores apply to them. AICapitalBurdenRelocation20261012Exact already demonstrates 75/0 -> 0/75 equal total burden; reuse for financing incidence, NOT proof of actual household losses. Existing AIEnergyCapitalBottleneck20261016Exact, AIGeometricMarketStressOperator2026Exact, AIFixedBasketMarketSeries20261012Exact, AICapitalRuntimeAuthorityParity2026Exact, AICoreWeaveSameObjectFinancingMaxCut20261016Exact located by filename; inspect semantics before import.

dashiTRADE #1 (head metadata da674329): signals/ai_capital_graph.py inspected: SourceReceipt(source_id,url,observed_at); CapitalEdge typed kind, endpoints, nonnegative finite weight, unit, independent_terminal_cash; CapitalGraph enforces one unit, scope and coverage. Do not add signed FX or price changes as cash edges; keep temporal event attachment separate and resolve into compatible monetary graph only on actual transaction receipt. signals/ai_market_event_series.py inspected: event-level direction flips and IPO withdrawals, explicitly gates fixed-basket collapse/vol/flip claims false. Its _signed currently maps malformed input to 0 and does not establish chronology; new adapter must reject missing direction or retain unknown, and check as-of ordering. Existing ai_capital_history, ai_capital_nonfactorability, ai_capital_burden_relocation and component trajectory modules located; reuse after source inspection.

#1131 (d1f5c91b): inspected EpsteinBearStructuredFundRecoveryRound20261015Exact: respondent pleading EFTA00294820 recounts $3m February 2007 COUQ redemption; EFTA00294835 recounts near $3m FTC and over $3m YLK winddown receipts (different bounds); EFTA00294821 describes 2008 assignment; EFTA00597963 collective $9.2m settlement, allocation open. Gross contribution != net loss; settlement != merits. Existing EpsteinBannonAICapitalReflexivityCrossPollinationExact, EpsteinFinancialInfrastructureEverything20261014 and ClaimIndexedEvidencePolarityExact located. #1131 file listing hit 3000 entries; not exhaustive.
#1245 (bedc0148): inspected docs/research/bannon-epstein-mortgage-chronology-adversarial-20261024.md: EFTA01600824 narrative and independent agency chronology already reconciled; no repeat. AustralianPensionThreeSenateInquiriesSourceReuseMaxCut20261027 and AustralianPensionWork2022TemporalSameObjectMaxCut20261027 located; Australia pension evidence does not establish US 401(k) holdings.
#1443 (a1a6bea9): AICaptureEpsteinTechEvidenceBridge20261101Exact, AIContinuingCapitalFundingMaxCut20261102Exact, AIOffBalanceCapitalRecovery20261101Exact and scripts/ai_capital_cycle_network_20261102.py located. #1291 (ed40b5a2 metadata) native hyperfabric donor, exact owner paths still to inspect (PR file listing incomplete for this purpose). No cross-branch imports assumed.

Revised acceptance: P0 PARTIAL existing historical/AI source atlases; only new dated source deltas and crosswalk open. P1 PARTIAL existing state/graph/trajectory; missing bitemporal event attachment and same-object causal-face bridge. P2 PARTIAL existing stress/event carriers; FX funding, IPO allocation and $100 actual threshold response open. P3 PARTIAL existing burden relocation/energy/pension donors; actual US retirement holdings and China physical/strategic receipts open. P4 PARTIAL existing parity/rival fit/nonfactorability; new event readback and exact-head local validation open. P5 roadmap committed. Branch metadata head bbdab7b0 conflicts with branch file readback containing prior b267178 update; retain explicit blob receipts, do not claim head coherence until verified.

Next executable minimal cut: attach event/disclosure/knowledge/settlement timestamps and reference existing graph scope/receipt; compare as-of eligibility, not infer intent. Add synthetic counterexamples using existing outcome and nonfactorability owners. Preserve all current terminal authority residuals. No claim of code execution or proof checking in this audit.


### Fresh master-based integration PR — 2026-11-21

Default branch is master. #1131 remains open/unmerged by PR metadata, but the selected cognition and economics owners exist on master, including identical previously inspected blob 332130df (Bear recovery), 64ba98a (time series), 4ee124e (outcome fit), 0fd5db2 (burden relocation), 1640018 (mortgage chronology). #1443 evidence bridge and #1245 mortgage chronology also present. Do not merge wholesale or duplicate prior work. Existing master owners inspected: JPYJGBTreasuryFundingTransmission2026Exact (be779a2: seven-coordinate YenFundingValve, CrossMarketFundingBridge, direction vs velocity); GlobalFundingLiquidityRealisationExact (1eb91bf: latent loss plus funding constraint plus collateral pressure); GeopoliticalEnergyAITreasuryTransmissionExact (0877644: candidate oil, gold, compute and JPY edges and multi-objective dollar state); AIGlobalFundingRegulatorySynthesisExact (13e7f52: CoupledState); AIGlobalPoliticalEconomySourceAtlas2026Exact (b9c4969: IPO timing and source attribution); CommonFactorStructuredFinanceExact (805f04b: common underlying driver, separate validator bias); ChinaEconomicLeadershipCrossSourceJoinExact (0175d2a: official/independent dimensions, not winner scalar). ChinaRetailGoldMarketTopology2026Exact (65cd7ea) already records official ICBC June 24, CCB June 25 and PSBC March notices, July 24 effective settlement for ICBC/CCB, with physical and accumulation products retained; avoid reacquiring these as if entirely absent. The specific claimed true-price warning still open. OpenWorldTemporalPromotionExact (83b3a67) already retains encounter state; ClaimIndexedEvidencePolarityExact (9ebaefd) preserves contextual opposition; TrialecticBoundaryFaceNonfactorabilityExact (4b0bd11) supplies 27 boundary states and consumer non-descent. TypedHyperfabricCore at guessed DASHI/Core path returned 404: locate correct path before import.

New source-written MacroFinancialTemporalConsumer20261121Exact.agda attaches relative common-clock event/disclosure/actor-knowledge times with as-of witnesses, keeps settlement separately typed, carries original coupled state/capital point/gold boundary/burden state without reconstructing them, and applies canonical ConsumerDescent witness to identical observable attachments with distinct synthetic correction objectives. This is a structural counterexample, not empirical intent identification. No assertion that these fields necessarily describe the same real-world event: scope/actor/source alignment, clock conversion and original state dates remain explicit next obligations. No new causal or terminal authority. Existing refinancing fit and candidate yen bridge retained unchanged.

P0 PARTIAL: reconcile fresh primary-source November delta only; P1 SOURCE-WRITTEN first attachment, native indexed hyperfabric and semantic scope/clock weld OPEN; P2 existing funding and market mechanisms, new quantified competing yield/IPO threshold results OPEN; P3 existing gold topology, China leadership and burden relocation, new physical stocks and actual US household incidence OPEN; P4 kernel and runtime parity OPEN; P5 this master-based canonical roadmap migrated from #1101. No local Agda, CI, external source verification or dashiTRADE write in this cut. Preserve prior research attributions, user-originated yen correlation and rival leak timing hypotheses; no present-day criminal or command inference from historical network.


### 2026-11-21 — fertiliser, news velocity, sentiment and historical-finance crosscut

- China urea: Reuters 2026-03-13 reports China world's largest urea producer, estimated 76.5 Mt for 2026, with export quotas/permit restrictions, NOT a majority of world production. https://www.reuters.com/world/asia-pacific/china-taps-fertiliser-reserves-hormuz-closure-disrupts-global-supply-2026-03-13/ . Separate factory output, domestic demand, export permits and realised exports.
- Potash: USGS 2026 world minerals outlook shows ~13.5% of 2025 capacity for China, after Canada/Russia/Belarus; country order based on output differs (~13% China, typically third). https://pubs.usgs.gov/publication/sir20265081/full . Keep capacity vs production, K2O-equivalent vs product tonnes distinct. Insert nitrogen/potassium/food security into existing physical input and geopolitical funding faces; fertilizer cost shocks propagate through food CPI and policy responses rather than equating production share with export control.
- Leon Black: already covered by master Epstein/Black/Apollo modules and SEC/DOJ primary receipts; https://www.finance.senate.gov/ranking-member/newsroom/news/continuing-epstein-investigation-wyden-questions-leon-black-over-new-revelations-in-epstein-files-appearance-of-hush-money-payments-and-surveillance-of-women/ . Original Instagram reel's purported name mention NOT independently verified; keep transcript/source request, do not source-launder.
- CNN Fear & Greed Index: seven-component derived US equity sentiment proxy, not independent evidence of motive or market mechanism. https://www.cnn.com/markets/fear-and-greed . As-of fetch/publish/version, underlying indicator clocks, score 0..100 and component availability; test against VIX, credit spreads, put/call, safe-haven demand to avoid circular explanatory use and hindsight leakage.
- External information ingestion is out of scope for this public repository. This roadmap specifies only source-neutral inputs: publication/observation timestamps, provenance identifiers, as-of eligibility, economic state projections and testable market responses. Do not name, describe, depend upon or expose private implementation details.
- New source-written reference files scripts/macro_financial_event_clocks_20261121.py and tests/test_macro_financial_event_clocks_20261121.py: timezone-aware four-clock event carrier, fail-closed disclosure/knowledge ordering, stable market-clock ordering, as-of observer-receipt gate, missing move != zero, explicit signed flip, propagation delay and market-response lag, settlement separate, Fear/Greed publication gate. They are an adapter/test harness only; no new RSS ingestion, no exchange execution or verified alpha. Source-written not Python-executed here.
- Additional rival counterfactual: identical price paths and sentiment can occur under endogenous repricing, intentional tolerance, deliberate intervention, selective corporate disruption or contagion; observed sentiment cannot choose between them. Macro H0–H4 labels are scoped to this public economic analysis.
- Next exact consumer: attach source identifier, earliest verified publication, permissible public observation time, actor/venue receipt where independently available, and subsequent quoted or traded market response. Compute source-neutral lag intervals with uncertainty, microstructure costs and no assumption of executable alpha. A price move before local observation remains admissible.


### 2026-11-21 continuation — tested as-of price admission and five-regime interface

Accepted local Python 3.13 reference re-execution: **9/9 unit cases PASS** (local reconstruction of committed script and test content, not a repository checkout or CI). Chronological ordering is deterministic; arrival gate and market-quote as-of gate are both required; price movement earlier than this observer's local receipt remains allowed but cannot appear in the observer's prior information set; unknown return is not a measured flat return; timezone-naive timestamps rejected; score 0..100 and publication gate checked. Synthetic $100 downward and upward crossings tested against $99 placebo, with future quote suppressed. A crossing is not proof of behavioural support, options positioning, profitable execution or causality.

Source-written extension to MacroFinancialTemporalConsumer20261121Exact.agda: H0 endogenous, H1 tolerated, H2 deliberate correction, H3 selective corporate intervention, H4 disorderly contagion each have explicitly mapped synthetic objective labels; added SameObjectJoin record with evidence-required true gates for source/scope, time unit and market quote as-of comparison. It neither certifies any real-world join nor collapses the pre-existing unsatisfied causal-intent and terminal finance gates. Agda not installed locally and source was not kernel checked. Existing master Everything import not edited: the module is a dedicated candidate, not a certified aggregate.

Critical correction to prior classification: H0-H4 do not form a mutually exclusive ontology over real actors or times; the finite Objective carrier is only a single-case synthetic consumer negative control. Independent documentary receipts are needed to associate several simultaneous mechanisms. Fear & Greed contributes only published sentiment observation and cannot independently disambiguate cause.

Public-only discipline retained. Current contents contain no private project-specific pipeline labels or paths. Older Git history on the PR branch may still retain removed text; this update is content-level, not history rewriting. No connected private repository was modified. Next step: resolve branch history privacy separately if required, validate Agda exact-head on an environment with pinned compiler, and test source-grounded JPY/US Treasury yield sign opposition with actual dated market/funding measurements.


### 2026-11-21 — opposing US Treasury yield pressure max-cut

Recovered original canonical owners on master and #1532: JPYJGBTreasuryFundingTransmission2026Exact.YenFundingValve and CrossMarketFundingBridge; GlobalFundingLiquidityRealisationExact.FundingState (latent vs realised loss); GeopoliticalEnergyAITreasuryTransmissionExact.MultiObjectiveDollarSystem. No replacement ontology.

New DASHI/Economics/JPYTreasuryOpposingFlow20261121Exact.agda (source-written, NOT Agda kernel-checked) consumes the original owner types. Downward yield pressures: safe-haven Treasury buying, expected policy easing. Upward: Japanese repatriation, forced Treasury sales, supply/term-premium. Exact synthetic witnesses: first fixture downward=10/upward=6; second downward=2/upward=6; both share repatriation=3, forced Treasury selling=2. Therefore those JPY components alone do not determine the sign. TreasuryFlowJoin records common-horizon, unit/elasticity normalization, transaction and policy intent as unfilled source-gated fields. No factual actor motive follows from signed price changes.

New scripts/treasury_opposing_flows_20261121.py and tests/test_treasury_opposing_flows_20261121.py match these synthetic values and fail-closed common-basis gate. Five equivalent Python reference assertions PASS locally; local reconstruction was run because current container could not fetch repository via external DNS. This is NOT checked-out exact-head execution or an Agda proof certificate. No Agda executable detected; kernel pending.

Next empirical maximum cut: actual timestamped yen intervention announcement/execution/settlement; BOJ rate expectations and JPY/USD hedging basis; Japanese foreign-holding security-specific flows; Treasury auction tails, tenor, observed volumes and yield decomposition into policy expectation versus term premium; observable leverage liquidation; AI asset exposure and pension incidence; same-window as-of controls and actor-specific primary-source intent. Do not equate IPO investor orders with settled JPY-funded purchases. No real-data yield sign, refinancing saving, successful market intervention or causal-intent claim established.

P2 structural ambiguity paid in source-written mathematical fixtures and locally re-executed equivalent Python; actual observed and common-unit numeric measurement OPEN. P0 original source delta OPEN. P1 same-object as-of join OPEN. P3 US household incidence OPEN. P4 Agda kernel and exact repo-head tests OPEN. P5 updated. Public-only scope; no private-repository implementation reference.


### 2026-11-21 — coupled dashiTRADE #1 Treasury mirror

The public runtime has been extended **on its existing PR #1** (branch `agent/ai-capital-stress-runtime-20261007`), rather than copying its capital graph into Agda. New `signals/treasury_opposing_flow_20261121.py` consumes original `SourceReceipt`, an optional `AICapitalStatePoint`, five source-bounded named pressure channels, declared unit/window and an as-of cut. It preserves unknown/unadmitted values, fails closed on mismatched pressure units or windows, future receipts, invalid numeric pressure and duplicate channels. It never injects FX/bond-yield pressure into cash edges or infers actual trading authority.

Agda's original JPY funding, forced realisation and geopolitical dollar owners retain source ownership; new `JPYTreasuryOpposingFlow20261121Exact` supplies synthetic opposite-yield fixtures (8/2/3/2/1 and 1/1/3/2/1). `MacroFinancialTemporalConsumer20261121Exact` now imports that owner, attaches `treasuryFlow` to `ExistingStateAttachment` and records direct Agda fixture equalities for the runtime parity target.

Mirror implementation document in public dashiTRADE (not any private project): `docs/treasury_opposing_flow_20261121.md`. Both branches retain source-written, not locally kernel/pytest-accepted parity; the separate local five-case Python reference from an earlier equivalent model is not an exact-head acceptance of the new dashiTRADE adapter. Empirical FX intervention, flow basis, Japanese net security sales, UST auction yields, term premiums, identified AI credit exposure, and 401(k) fund holdings remain source-open. Final H0–H4 intent determination remains prohibited by the yield-sign consumer alone. No CI and no modification of private systems.
