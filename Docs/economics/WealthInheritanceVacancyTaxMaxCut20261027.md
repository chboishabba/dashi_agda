# Wealth, inheritance, vacancy and 100% cap: source-typed max-cut (27 October 2026)

**Research direction:** Johl Brown. **Source-written synthesis and finite formal adapter:** OpenAI ChatGPT assistance, 27 October 2026. **Original authors/institutions keep historical/empirical ownership** (listed below). **Status:** one Agda source module and independent bounded Python test; no Agda compiler or kernel receipt in this pass; no implemented Australian tax law, empirical treatment effect, or new economic theorem.

**Motivating materials:** two user-supplied pasted conversations: (1) Musk wealth, a 100% above-threshold proposal, FDR, vacancy taxation, inheritance versus wealth; (2) Marx, anarchisms, postmodernism, accelerationism, techno-feudalism, feminist and right-reactionary frames. These are prompts and second-hand assistant assertions, *not source roots*.

## 1. Max-cut: separate the objects before claiming policy effects

| Policy | Base | Trigger | Finite calculation / distinct residual |
|---|---|---|---|
| 100% marginal **annual income** tax | annual recognised income | income > threshold | excess of income above threshold; does not itself constrain total asset stock |
| 100% **stock wealth excess** tax | net wealth on valuation date | stock > threshold | excess of stock above threshold; valuation, title, global jurisdiction and liquidity unpaid |
| annual net wealth tax | assessed net asset stock | assessment period + threshold | rate schedule, tax credits, deductions; not the same as a hard cap |
| tax on unrealised asset gains | annual gain in appraised value | change of stock value | loss offsets and mark-to-market needed; not equivalent to levying all stock excess |
| inheritance/estate tax | transfer on death | legal transfer | lifetime gifts, trusts, estate versus recipient taxation remain essential |
| vacant homes tax | residential vacancy condition + property valuation | vacancy period and exemptions | observed physical status; not a test of 'idle shares' |
| tax on capital gains | legally realised gains | recognised sale/transfer | taxable event and basis; not property ownership alone |
| taxes on collateral-backed loans | enacted deemed-income base, if any | loan meeting defined collateral/use conditions | requires *new legislation*; collateralisation alone is not ordinary income |

The user's proposed 100% *wealth* ceiling is a policy design to analyse, **not enacted law**. In the finite nonnegative no-exemption illustration: tax due = max(wealth − ceiling, 0); post-tax wealth = min(wealth, ceiling). The analogous income-bracket formula is numerically similar **but differently typed**. Same flow, different wealth is a constructive negative control against conflation.

**New finite ownership/control witness:** two positions may have the same total net wealth (5 units) and identical hard-cap liability (2 units above a 3-unit threshold), yet carry 1 versus 7 voting-right units. Therefore even perfect tax-assessment arithmetic does not determine corporate control. This is a synthetic logical counterexample, not a claim about any living billionaire or tax system.

**Vocabulary correction:** the vacancy-tax analogy is useful only at the level of a *non-sale-triggered periodic assessment*. Vancouver imposes the tax because a dwelling is vacant; a global wealth cap imposes tax because assessed value exceeds a limit. A share that finances factories is not 'vacant housing' merely because the founder does not sell it. Productivity/exploitation/ownership are separate consumer-defined questions.

**Political-economy causal graph (hypothesis, not theorem):**

tax legislation + base definition + enforcement + asset valuation + ownership data
→ assessed liability → payment/avoidance/migration/liquidity/ownership responses
→ public receipts + distribution + real investment + political power + housing/care outcomes.

No single downstream outcome is deducible from the statute or a tax receipt alone. Democratic control over the use of revenues is another separate coordinate.

## 2. Original-source priority / source snowball

1. **Karl Marx and Friedrich Engels, 1848, Manifesto of the Communist Party, Part II.** Original authored transition programme proposes a heavy graduated income tax and abolition of inheritance rights. These are *not* all of Marx's later scholarship, an income-tax system equal to a 100% wealth-stock cap, or a proof that every current policy works. Root: https://www.marxists.org/archive/marx/works/1848/communist-manifesto/ch02.htm . Distinct prior DASHI owner: DASHI/Culture/MarxLabourUnionSourceBoundaryExact.agda (Capital I, labour and unions).
2. **Franklin D. Roosevelt, Executive Order 9250, signed 3 Oct 1942.** Salary limitation was 'insofar as practicable' and subject to allowances, with an after-tax $25,000 condition; it is not a universal confiscation of accumulated wealth. Presidential original: https://www.presidency.ucsb.edu/documents/executive-order-9250-providing-for-the-stabilizing-the-national-economy . National Archives order/changes: https://www.archives.gov/federal-register/executive-orders/1942.html . The exact 1943 statutory rider/implementation chronology merits separate enrolled-law join; do not equate all 1943 changes with repeal of EO 9250 itself.
3. **U.S. top federal individual income statutory bracket, FRED IITTRHB.** 94% in 1944 and 1945, 91% in most of 1954–1963; **1950 was 84.36%, 1951 91%, and 1952–1953 92%**. Source: https://fred.stlouisfed.org/data/IITTRHB . *Top statutory* != average/effective rate, and a tax rate does not itself explain the 'Great Compression'. The secondary Tax Foundation's 16.9% effective estimate uses a different historical dataset and a non-equivalent base: https://taxfoundation.org/data/all/federal/top-1-percent-tax-rate/ .
4. **City of Vancouver, 2025 Empty Homes Tax Annual Report, covering 2024 reference year.** Empty-homes rate 0.49% (2024); 67% reduction in declared/determined/deemed vacant homes from 2017 to 2024, and $194.3m allocated cumulatively to affordable housing in the report. The **City explicitly cautions that isolated causal attribution is difficult**. Tax rate 3% from 2021 reference year; market rent vacancy and taxable vacant-homes indicator must not be conflated. Source: https://vancouver.ca/files/cov/2025-empty-homes-tax-annual-report.pdf .
5. **State Revenue Office Victoria, 2026 VRLT.** Vacant *residential property* subject to 1%, 2%, then 3% of capital improved value for successive liable years in the ordinary case; specified undeveloped/new-land cases stay at 1%. All Victoria residential land potentially in-scope since 2025, with more undeveloped-land rules from 2026. Primary law/explanation: https://sro.vic.gov.au/owning-property/vacant-residential-land-tax/understanding-vacant-residential-land-tax ; rates: https://sro.vic.gov.au/about-us/rates-and-statistics/current-rates/vacant-residential-land-tax-current-rates . **No supplied causal evaluation** of the statewide 2025 expansion.
6. **OECD, 2018, The Role and Design of Net Wealth Taxes in the OECD.** Reports multiple repeals, tax-base/valuation challenges, but also Switzerland's 2016 net-wealth tax revenue around 3.7% of its total receipts, and stresses transparency, administration, capital taxes and country-specific design. Root: https://www.oecd.org/en/publications/the-role-and-design-of-net-wealth-taxes-in-the-oecd_9789264290303-en.html .
7. **OECD, 2021, Inheritance Taxation in OECD Countries.** Wealth-transfer taxes in 24 of 36 covered OECD countries; average just **0.5%** of all tax revenues in 2018 among those levying these taxes; evaluates distributional, design and exemption options. DOI https://doi.org/10.1787/e2879a7d-en . Existence of inheritance tax != proven end to family corporate power; tax bill != automatically control redistribution.
8. **Katrine Jakobsen, Henrik Kleven, Jonas Kolsrud, Camille Landais and Mathilde Munoz, 2026, AER 116(10), DOI 10.1257/aer.20241596.** Primary research on Scandinavian administrative data: 1 percentage point increase in top wealth-tax rate associated with ~2% lower stock of wealthy taxpayers; aggregate effects in model/estimates: employment −0.02%, investment −0.07%, value added −0.10%. A *strong positive control for measured migration* but a **negative control for sweeping 'massive capital flight destroys the economy' claims**. Exact generalisability and identification assumptions remain study-relative. Source https://doi.org/10.1257/aer.20241596 .
9. **Gabriel Zucman, 25 June 2024, G20-commissioned blueprint.** A proposed 2%-of-wealth annual minimum for billionaires, estimated $200–250bn global receipts annually; international cooperation, exit tax and asset transparency are specified implementation mechanisms. *Proposal/estimate, not enacted legal regime*. Source: https://taxobservatory.world/www-site/uploads/2024/06/report-g20.pdf .
10. **Current-billionaire control:** Forbes original June 12 2026 coverage of the SpaceX IPO states Musk briefly crossed $1tn, then declined; as of Forbes' **1 October 2026 snapshot** it placed him at $936bn. Thus "he is a trillionaire now" is a date-dependent empirical claim, not a permanent status. Sources: https://www.forbes.com/sites/mattdurot/2026/06/12/spacexs-ipo-just-made-elon-musk-the-worlds-first-trillionaire/ and https://www.forbes.com.au/news/billionaires/top-10-richest-people-in-world/ . No exact 27 October mark asserted.
11. **South Korea positive financial transfer control:** Yonhap, 9 Apr 2026, reports completion of approximately ₩12tn Lee-family inheritance-tax payment after share sales, including 15m Samsung Electronics shares sold by Hong Ra-hee. Does **not** prove Samsung family voting control became decentralised. Source: https://en.yna.co.kr/view/AEN20260409002400320 .

### Independence ledger

The Vancouver report, its municipal dashboard, and articles reproducing the report are **one administrative source root**, not three independent replications. OECD 2018 net-wealth and OECD 2021 inheritance reports are distinct products but not experiments establishing the same outcome. The Forbes June original, later headlines and live listings are *successive market valuations*, not a timeless fact. The OECD and Zucman proposal describe different research and policy roles; only legislatures can enact them. Empirical effect studies must retain author/cohort/treatment/unit/time and design.

## 3. Political-philosophy claims: attribution severity

The second pasted source treats broad traditions as if each made one unified tax-policy proposal. This is not justified. Preserve a **four-axis matrix**:

* **Descriptive critique:** who owns productive capital, infrastructures/platforms, labour and care; how wealth concentration may shape power.
* **Normative objective:** redistribution, abolition of private capital ownership, decentralised mutual aid, gender/care justice, acceleration of technical production, or property-right prioritisation.
* **Institutional mechanism:** marginal income tax, capital stock levy, worker control, inheritance limits, public platforms/utilities, care provisioning, or no state taxation.
* **Source authority:** direct primary authored statement, later interpretive school, secondary scholarship, or our hypothetical policy design.

Marx and Engels' 1848 proposals are **primary authored claims**. Claims like "all anarchists agree that taxes are absurd", "Baudrillard says asset valuation is unreal", "Nick Land has demonstrated AI capitalism's inevitable victory", "all fourth-wave feminists recommend algorithmic accountability taxes", or "e/acc implies a specific tax policy" are **unsupported as school-wide statements in the supplied text** and must not be canonised. Anti-statist anarchism and anarcho-capitalism are not interchangeable movements. A theorist's metaphor or polemic is not an economic causal model. Any future module should have the theorist's *actual primary text* and a precisely limited position.

## 4. Severe BIDI hypotheses and discrimination

| Proposition to test | Strongest charitable mechanism | Rival explanation / severe test |
|---|---|---|
| 100% annual wealth cap reduces oligarchic control | requires beneficial-ownership tracing and real transfer/voting-right outcome | legal control may persist via trusts, options, nominees, mergers; measure post-tax control not merely receipts |
| High wartime tax rates created postwar equality | very high top marginal rates discourage extraction | WWII mobilisation, wage-setting, unions, New Deal, demography and differential capital destruction confound; model postwar 1946–1963 without attributing causality by chronology |
| Vacancy taxation returns houses to use | annual liability makes leaving a home empty costly | simultaneous BC/federal taxes, housing market and occupancy data changes; staggered treated/control units and enforcement audits |
| Annual wealth tax causes economy-wide collapse | wealthy owner relocation can affect firm activity | AER 2026 identifies migration plus small modelled aggregate effects; measure same population employment/investment/tax receipts |
| Estate taxation disperses dynastic corporate control | heirs must pay, sometimes selling shares | voting shares, differential rights, trusts and funding loans may preserve control; legal control graph before/after transfer |
| AI tax audits solve wealthy evasion | ownership-graph matching, anomalies and third-party reporting | wrong legal base, false positives, privacy bias and appeal rights; prospective audited enforcement effect and procedural fairness |
| Idle equity is equivalent to vacant housing | wealth held without sale may appear 'hoarded' | firms can deploy productive capital while founder retains shares; require a separate measurable idle-use construct |

## 5. Pareto roadmap and acceptance cut

**P0 paid in source:** distinguish seven tax bases, disjoint constructors and finite 100%-excess examples. Typed receipts with actual original authors. Bare tax-policy categories do not claim econometric proof.

**P1 partially paid / immediate:** independently rerun finite test, formally typecheck exact Agda source when compiler available, and obtain exact-commit kernel receipt. The existence of \`refl\` and empty-type restrictions in source is **not** an executed Agda proof certificate.

**P2 highest economic discriminant:** specify actual stock valuation/beneficial title versus legal residency and worldwide assets for proposed cap. Add multi-period transition including investment return, lending, forced share issuance and equity control changes. Do **not** treat tax liability as realised payment.

**P3 causal design:** Vancouver policy versus market and concurrent taxes; empirical validity of 2026 Scandinavian estimates under alternative control samples and macro regimes; postwar peacetime counterfactual, with labour/union/war mobilisation confounders explicitly modelled.

**P4 political/governance consumer:** tax revenue versus democratic allocation; gendered unpaid-care impacts with original time-use surveys; labour/control/collective-ownership and platform rent, keeping theory and empirical results distinct.

**P5 only when source-root available:** author-specific Land/Varoufakis/Baudrillard/Crenshaw/hooks/Bakunin/Kropotkin/AnCap/e-acc original-text quotations, avoiding synthetic 'the school believes' positions.

### Cross-PR inspiration (read-only reuse)

* Agda #1275: source-typed Zipf family distinguishes definitions, observed regularities, falsifiers; reuse its **separate policy base / no-universal-consequence** pattern.
* Agda #1267: charitable steelman and adverse rival models rather than automatic ideological confirmation.
* Agda #1276: same-object legal/beneficiary timeline and no unproven motive promotion.
* Agda #1245: institution/financing/ownership-source joins are not hidden coordination without exact transmission evidence.
* Existing DASHI Core AttributedSource and SnowballAttributionProvenanceInvariant owners remain authoritative. No new global ontology or attribution substitution required.

**Stopping wall:** no original global beneficial-ownership/tax return panel, defensible counterfactual for the proposed 100% wealth-stock cap, or same-person political-control outcome; there is no honest empirical effectiveness proof beyond the cited study-relative estimates. Coding a toy tax function cannot pay this empirical wall.

## 6. Verification command / result categories

\`python3 scripts/check_wealth_tax_maxcut.py\` exercises a finite arithmetic domain and constructive non-factorisation witness. It is a **local computational check only**. The Agda module supplies source-written theorem candidates and definitional proof terms; a compiler invocation and complete dependency closure remain unverified here. Legislative and historical facts are primary-source/peer-reviewed-source receipts, not theorems proved by Agda.
