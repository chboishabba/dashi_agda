# Financial iceberg K0 recut: continuing capital cycle and bounded funding — 2 November 2026

## Executive finding

The earlier CoreWeave 2027–2031 `50% annual OCF growth / 20% investing growth`
experiment was **not a system solvency model**, a full CAPEX asset-vintage model,
or a borrower–lender–customer model. The `USD120.730bn` cumulative baseline
gap omits the fact that future liquidity comes from somebody who expects a return.
The narrower `USD37.046bn` peak was a **different** 50% OCF-growth and **flat**
investing baseline. Those are not competing observations and must never be
interchanged.

New implementation:
- `scripts/ai_capital_cycle_network_20261102.py`: annual *financing-supply
  constrained* continuation model and conditional loss-incidence waterfall.
- `DASHI/Governance/AIContinuingCapitalFundingMaxCut20261102Exact.agda`:
  finite reused-owner theorem: identical current-maturity views cannot determine
  whether future GPU/energy expansion and independent cash service are funded.
- Existing lower-level
  `DASHI/Governance/AIOffBalanceCapitalRecovery20261101Exact.agda` is retained.
  Earlier `DASHI.Economics.AIInfrastructureConsumerIndexedFibreAdequacyExact`,
  `AIInfrastructureConsumerFibreRefinementSchedulerExact`,
  `AIStructuredInfrastructureCommonFactorRiskExact`,
  `GlobalFundingLiquidityRealisationExact` and the K0 owners on draft #1101
  retain first theorem priority; no copy of unmerged sibling proofs.

## Original observations and careful accounting

**CoreWeave primary source:** SEC 10-Q for 2026-06-30,
https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm
- Six months OCF +USD3.663bn, investing cash −USD14.874bn, financing
  +USD13.985bn; annualised baselines 7.326 and 29.748 USD bn are **model
  conventions** rather than actual full-year amounts.
- Cash USD5.524bn, marketable USD0.015bn, and UNUSED SECURED BORROWING
  AVAILABILITY USD10.014bn: disclosed USD15.553bn 'liquidity' is not free
  company cash. The model retains a synthetic USD1.5bn minimum operating reserve.
- H1 cash-flow reconciliation reports **+USD1.365bn deferred revenue movement**.
  A source-written Agda identity `2298+1365=3663` permits a synthetic
  `USD2.730bn annualised reduction` sensitivity on OCF, but this is **not**
  a claim that all customer prepayments are fictitious, one-off, or the only
  working-capital item. The reported cash is real; the cash-conversion and
  terminal independent payer are the open questions.
- USD35.6bn recognized borrowing is a dated separate stock. A `17%`
  assumed *2027* refinancing tranche (USD6.052bn) is a scenario assumption
  from secondary maturity commentary, **not** asserted as an original facility
  maturity schedule. Successful rolling replaces debt: gross issuance counts
  original principal *once* and new money separately; only an incremental
  assumed 4% pricing premium is added over baseline OCF's existing interest.

**Meta original:** https://www.sec.gov/Archives/edgar/data/1326801/000162828026066773/meta-20260930.htm
Q3 2026 USD355.73bn uncommenced future leases; USD454.52bn commitments,
USD121.41bn commitments due 2027; USD10.80bn escrow-restricted money-market
funds not free for other liabilities. Uncommenced undiscounted rent, current
recognized lease liabilities, contract obligations, restricted cash, conditional
residual-value guarantees, and SPV borrowing are **distinct**. Categories may
overlap, and only specific agreement/source identities permit elimination.
Do not sum Meta's figures with CoreWeave's credit or SoftBank's equity as if
independent terminal spending.

**SoftBank original:** issuer Sept24 2026 USD10bn bond takeout
and October1 original issuer confirmation the preceding USD40bn bridge is fully
repaid/cancelled. Prior `SoftBankOpenAIValuationLeverage2026Exact` owns this
finance evidence and mark-to-cash boundaries. SoftBank OpenAI equity is NOT
independent end-user expenditure just because it funds investment.

**Macro original:** RBA October Financial Stability Review identified overlapping
AI finance / SPVs / guarantees and possible market repricing, not an executed
rescue. The prudential/macro scope and Australian financial-system exposure
cannot be extrapolated mechanically to all US non-bank holders.

## Executed local numerical stress test (independent equivalent code)

The authoring session executed and checked equivalent local Python equations,
including stop-at-first-unfunded-year logic. The GitHub-committed script is
source-written and **not directly executed from a checked-out repository**.

All USD billions, 2027–2031. First five rows preserve 50% yearly operating
cash growth and 20% investing growth; additional parameters are specified:

| Scenario | Peak modeled cash gap* | New debt drawn (incl secured credit) | Gross issued incl assumed rollover | First supply block |
|---|---:|---:|---:|---|
| Old full-financing envelope, no initial cash | 120.730 | 120.730 | 120.730 | none by assumption |
| USD4.039bn free start cash, full conditionally drawable secured line | 120.730 | 116.691 | 116.691 | none by assumption |
| Plus 12% incremental coupon on new borrowings | 152.994 | 148.955 | 148.955 | none by assumption |
| Plus **one-year cash receipt lag** and **extra** 20% refresh cost from 2029 | 250.725 | 246.686 | 246.686 | none by assumption |
| Plus 15% reduction in modeled OCF from 2029 | 263.543 | 259.504 | 259.504 | none by assumption |
| Plus 16% new-money coupon and 4% premium on assumed 17% debt refinance | 282.413 | 278.374 | 284.426 | none by assumption |
| 12% new coupon plus synthetic H1-deferred-revenue OCF normalisation | 215.836 | 211.797 | 211.797 | none by assumption |
| 12% new coupon + max USD20bn **other new money per year** | stop in 2028 | 2027–28 partial | 2027–28 partial | 2028, USD8.834bn continuation hole |
| 12% new coupon + max USD10bn **other new money per year** | stop in 2027 | 2027 partial | 2027 partial | 2027, USD0.656bn continuation hole |

*The unconstrained peak is a cash gap **if the proposed build-and-customer
trajectory gets built and paid for**. It is not a liability existing today and
not a solvency forecast. Under a financing cap, the model **stops** at the
first unfunded build; a five-year 'peak' cannot be projected after that event
without specifying a restructure, project cancellation, rationing or new
financing. Likewise, net cost of capital would depend on covenants, financing
mix and maturity/refinancing vintages not captured here.

**2027 maturity sensitivity:** the optional 17% × USD35.6bn = USD6.052bn
tranche is fully rolled in the stress, so it contributes to **gross issuance**
but not a second capex or existing-principal cash outflow. Existing coupon costs
are already in H1 OCF; only the extra 4% refinancing spread is added. Same
source principal appearing as customer receivable, SPV project note and vendor
sale is not three different external-demand dollars.

## Contract waterfall and actual systemic risk

A purely synthetic USD15bn project-debt instrument with recoverable
collateral USD10.5bn has a USD4.5bn shortfall. With *an assumed* triggered
USD5bn capped sponsor guarantee, the model allocates USD4.5bn to the sponsor
and zero to lenders; with no trigger it allocates USD4.5bn to lenders.
**Neither USD15bn, the USD5bn cap, nor the trigger is a Hyperion actual
contract amount.** This proves the importance of the same-object recovery
and contractual step-in/waterfall documents before attaching systemic exposure
to a lender, Meta, bank, insurer or pension.

A proper 2008 comparison also requires lender-to-counterparty concentration,
collateral-vintage co-variation, rehypothecation/security/repo rights where
actual, cross-default triggers, and actual realised losses. Treat financial
stress and bailout as distinct states; the original repo
`GlobalFundingLiquidityRealisationExact` already proves latent stress cannot
automatically promote to forced realisation.

## Second-/third-order iceberg join

An inability to finance delivered compute → delivery and customer renegotiation
→ collateral repricing and credit rollover compression → systemic-stability
political incentives → possible public/private reorganisation or extra
government operational controls → **measured** contraction or expansion of
independent model execution. A state/public backstop can also preserve
competition if interoperability and model-independent operation are enforced.
The last instrument, legal authority and access result are **not source-paid**.

## Exact remaining K0→K6 priority

- **K0a**: same-project actual commencement-date and lease/contract overlap
  reconciliation (Meta, and separately CoreWeave/Oracle, never aggregate
  unlike company scopes).
- **K0b**: original CoreWeave lender annex/covenant/cash-sweep/draw conditions,
  maturities for each instrument, collateral description, customer prepayment
  cash conversions, cancellation and demand concentration. Earlier open #1101
  retains source ownership for these original contracts.
- **K0c**: GPU vintage-by-vintage useful life, hardware residual auction data,
  next-gen throughput economics, delivery lag, power/cooling connection dates.
- **K0d**: identify true external final payers and settle invoice/bank receipts
  independently of partner financing or annualised ARR/backlog claims.
- **K0e**: debt-supply empirical estimate by firm/instrument/period, including
  actual bond/loan amounts, collateral haircuts and whether lender can delay a
  draw. The hypothetical USD10/20bn annual supply ceilings are NOT estimates.
- **K1**: working independent inference/knowledge-validation route under
  physical/capital/provider-coalition attack and affordable business limits.
- **K2**: actual rescue/administrative policy instrument and rights transferred
  to buyer/sponsor/state, plus counterfactual multivendor route.
- **K3**: private-credit/pass-through/bank/pension and insurer risk propagation
  with identity-qualified lender positions and covariance; compare to 2008
  without presuming identical securitisation or fraud.
- **K4–K5**: explicitly attributed ideology and Epstein historical network
  adjacency must acquire *new present-day policy/contract-specific* receipts.
- **K6**: exact committed Python script execution, focused and aggregate Agda
  typecheck using pinned repo toolchain, independently source-verified runtime
  receipts and documentation consistent with observed output.

**Stop/promotion rule:** missing real finance, adoption, or model execution
is a named empirical obligation, never manufactured from a finite countermodel.
Original source authors retain ownership of financial reports; prior DASHI
theorem/PR owners remain credited as prior mathematics. No ESD edits.
