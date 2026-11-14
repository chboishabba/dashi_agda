# 2026-11-01 — AI off-balance commitments, growth-debt and rollover max-cut

This is an original-issuer, **attribution-sensitive** companion to
`Docs/KnowledgeProcessingSovereignCaptureMaxCut20261101.md`.
Golden source module: `DASHI/Governance/AIOffBalanceCapitalRecovery20261101Exact.agda`.
Executable assumptions: `scripts/ai_off_balance_growth_stress_20261101.py`.
Do not infer a systemic rescue, fraud, re-hypothecation, consolidated legal debt or illegitimate regulation from economic exposure alone.

## What is actually financed and what is NOT on the balance sheet

1. **Borrower debt and recognised leases**: balance-sheet notes/loans, seniority, recourse, restricted entities, current and future interest. CoreWeave SEC [30 June 2026 10-Q](https://www.sec.gov/Archives/edgar/data/1769628/000176962826000366/crwv-20260630.htm) reported USD35.6bn debt, USD16.3bn recognised operating-lease liabilities, USD5.524bn cash and USD10.014bn unused secured credit commitments; company total liquidity USD15.553bn includes the latter and USD15m marketable securities. These are separate roles, not a single fungible cash pool.
2. **Leases signed but not commenced**: [Meta SEC 30 September 2026 10-Q](https://www.sec.gov/Archives/edgar/data/1326801/000162828026066773/meta-20260930_htm.xml) USD355.73bn; up USD76.74bn (+27.51%) from [June 30 USD278.99bn](https://www.sec.gov/Archives/edgar/data/1326801/000162828026050705/meta-20260630.htm) and up USD172.85bn (+94.52%) from March 31 USD182.88bn. Microsoft FY26 annual report separately USD329.1bn not-commenced leases: https://www.microsoft.com/investor/reports/ar26/. Future undiscounted rent is not the current recognised debt principal. Commencement timing, conditional clauses, inflation adjustment and discount are different fields.
3. **Noncancellable service/purchase commitments**: Meta September 2026 USD454.52bn, ~USD121.41bn due in 2027, plus **separately** up-to USD14.72bn contingent cloud commitments. Scope includes cloud, servers, infrastructure, energy and consumer hardware, not all AI. The USD454.52bn category may overlap uncommenced lease obligations and other presentations: **DO NOT SUM with USD355.73bn or the USD84.0bn note principal** without footnote mapping and elimination. Likewise the ~USD1.09tn Reuters August five-firm uncommenced lease compilation is a cross-company contemporaneous snapshot, not a summed all-sector debt line: https://www.reuters.com/business/retail-consumer/ai-data-centre-race-builds-1-trillion-lease-burden-big-tech-2026-08-04/ .
4. **SPV project debt and contingent sponsor recourse**: [Meta and Blue Owl original 21 October 2025 joint venture](https://investor.atmeta.com/investor-news/press-release-details/2025/Meta-Announces-Joint-Venture-with-Funds-Managed-by-Blue-Owl-Capital-to-Develop-Hyperion-Data-Center/) specifies approximately USD27bn capital budget, 80% Blue Owl fund / 20% Meta JV ownership, third-party bonds, Meta tenant commitment after construction, and a **conditional capped residual-value guarantee for 16 years** if leases expire or are not renewed. Non-consolidated borrower debt is different from unconditional Meta debt; guarantee still transmits economic risk back to Meta and must be modelled with trigger, cap and collateral recovery.
5. **Vendor and lender circular flows**: original pre-existing owners `DASHI.Economics.ReflexiveFlowValidationExact`, `AIFinancingReflexivityExact`, `CoreWeaveGPUBackedStructuredFinance2026Exact`, `AIStructuredInfrastructureCommonFactorRiskExact`, `AITerminalPayerEconomicValidationExact`, and open #1101 provide the source/typed drivers. Separate: vendor invests in customer, customer promises compute purchase, SPV borrows to deliver, collateral tied to GPUs, terminal users pay independently (not automatic). Multiple SPVs using the same ultimate customer or chip value are not independent risk.
6. **Backlog / future revenue**: [CoreWeave original June 2026 SEC earnings exhibit](https://www.sec.gov/Archives/edgar/data/1769628/000176962826000362/coreweave2q26earningspress.htm) reports ~USD104bn backlog conditional on delivery/availability, explicitly excluding >USD25bn early-Q3 additions. This is **not free cash**, contains execution, timing, cost and counterparty risk and cannot be added to cash.
7. **SoftBank parent credit and project structure**: prior `DASHI.Economics.SoftBankOpenAIValuationLeverage2026Exact` correctly owns earlier USD40bn bridge and OpenAI capital investment. [24 September 2026 original issuer terms](https://group.softbank/en/news/press/20260924) issued USD10bn BB+ unsecured notes at 8.625/9.25/9.75% coupons, weighted 9.4125%, annual contractual coupon USD941.25m (plus separate EUR1bn notes not included). [1 October 2026 issuer release](https://group.softbank/en/news/press/20261001) confirms third USD10bn tranche, cumulative OpenAI investment USD64.6bn / approx 13%, and that **the old USD40bn bridge was fully repaid and cancelled**; do not double-count it with takeout notes. [CFO 2026 report](https://group.softbank/en/ir/financials/annual_reports/2026/message/goto) deliberately seeks nonrecourse project finance that does not enter SoftBank parent loan-to-value, subject to project legal and funding conditions.

## Empirical current stress versus *future-growth funding clock*

CoreWeave original first-half 2026 cash-flow statement: operating +USD3.663bn, investing −USD14.874bn, financing +USD13.985bn. The **pre-financing difference is −USD11.211bn in six months**, annualised *for experimental calibration alone* to operating USD7.326bn and investing USD29.748bn. Investing/operating ratio = **4.0606**. The reported USD15.553bn liquidity is largely **not freely held cash**.

A five-year (2027–2031) toy envelope grows operating cash and investing spend independently. Both *cumulative 2027–31 shortage* and *peak temporary external-financing need* are reported, because later-positive cash cannot fund earlier contractual obligations:

| OCF growth p.a. | Investing spend growth p.a. | Net shortage, USD bn | Peak funding required, USD bn | First annual free cash after investment |
|:--|:--|--:|--:|:--|
| 30% | 0% | 62.615 | 62.615 | None through 2031 |
| 50% | 0% | 3.823 | 37.046 | 2030 |
| 50% | 20% | 120.730 | 120.730 | None through 2031 |
| 75% | 20% | 2.176 | 55.420 | 2030 |
| 100% | 20% | -188.565 | 34.579 | 2029 |

The implausibly extreme 100% sustained OCF growth row is a sensitivity control, not a forecast. These totals exclude debt amortisation, taxes outside reported OCF, new borrowing interest, asset-sales, resale/redeployment, changing GPU prices and present available cash. No present solvency conclusion follows. A long-dated current loan **does not fund future refresh capex automatically**, particularly if new assets have to be procured repeatedly to fulfil a growing backlog.

**Synthetic lease PV test** (do not add to recognised debt): if Meta's USD355.73bn *undiscounted* not-commenced lease total were paid evenly for 20 years starting immediately, PV at 5/8/12% discount rates would be **USD221.659bn / 174.630bn / 132.855bn**. Other 15/25-year conventions are printed by the script. Actual lease commencement across 2026–2036 and 1–30-year terms invalidates this as a GAAP booked amount; it is a sensitivity envelope only.

**Residual-risk return to sponsor:** the Hyperion residual guarantee cannot be numerically called without actual non-renewal trigger, appraised asset value, guarantee formula, capped amount, debt priority and shareholder recovery. Worst-case bondholder losses cannot be estimated by applying Meta's overall credit spread to SPV debt; they have different claims and loss waterfalls.

## Ed Zitron original author and citation classification

The October original commentary is now directly recovered:
- Ed Zitron, [Credit Crunch](https://www.wheresyoured.at/credit-crunch/), 6 October 2026.
- Ed Zitron, [Annualized Enron Rate](https://www.wheresyoured.at/annualized-enron-rate/), 13 October 2026.

His arguments focus on continuing external financing, off-balance project debt, elevated rates and misleading run-rate/gross-net narratives. These are **attributed authored interpretations**; original SEC issuer footnotes remain the higher-grade source for their own numeric/legal statements. The general code search over `dashi_agda` and PR titles did not identify a prior *Ed Zitron-named file owner*, but that does not establish absence from all branches or adjacent repositories. Keep prior `SoftBankOpenAIValuationLeverage2026Exact` and financial source modules as the pre-existing mathematical owners.

## Second and third-order counterfactuals

- **First:** AI workload demand and infrastructure spending, signed contracts, financed installations, disclosed issuer profit/cash and lender origination.
- **Second:** lower developer borrowing capacity, higher cash collateral, vendor-financed sales cycles, depreciation/refresh pressure, SPV refi distress and risk transmitted through parent tenant obligations/guarantees. Different SPVs need not mean diversified ultimate demand.
- **Third:** private-credit asset markdowns, impaired pension/insurer exposure, pressure for customer/taxpayer stabilization, consolidation of compute operators and rulemaking over permissible independent compute. The final public rescue/exclusive knowledge-control transition has **not** been evidenced from these commitments alone.
- **Countervailing branch:** project cancellations, ordinary private restructuring, genuine multitenant external demand, refinanced debt with reduced leverage and interoperable independent compute. Test these as counterfactual paths without inventing expected probabilities.

Distinct legal and fiscal incidence of the burden — equity loss, senior secured recovery, tenant loss, project-finance guarantee, bank credit exposure, government contingent support — is essential for a valid 2008 structured-credit comparison.

## ZKP O/R/C/S/L/P/G/F and status

O: user-directed financed-knowledge monopoly stress; R: future demand, funded capability, user exit; C: golden Agda source bridge and local Python numerical checker; S: no unsupported fraud or secret-control declaration; L: contract scope, guarantee and payment waterfall; P: exact source-written arithmetic and branch readback, **Agda kernel not run**; G: independent issuer accounting and commentary attribution, no ESD edits; F: empirical debt and lease vintage cohorts, upgrade edge-by-edge.

**Remaining exact payment cut**: (a) issuer- and facility-specific lease/contract overlap eliminations, (b) independent terminal payer bookings and customer payment lineage, (c) GPU depreciation and refresh schedule matched to each customer contract and debt tenor, (d) capital call/contingent guarantee waterfall and actual SPV balance sheet, (e) lender correlated risk across CoreWeave/Oracle/Meta and actual risk-transfer holders, (f) time-series of borrowing prices, covenant headroom and exit outcomes, (g) exact-head Agda kernel compilation and **actual execution of committed Python script** (independent equivalent arithmetic was locally run), (h) match any financial-policy intervention to real legal authority before asserting sovereign ownership.

**Attribution:** SoftBank, CoreWeave, Meta, Microsoft and RBA issuer originals as source roots; Ed Zitron as named author of commentary; earlier DASHI economic/structured-credit owners remain their own independent mathematics and attribution; this is a new consumer-specific exact source bridge, not authorship of the older mechanisms.
