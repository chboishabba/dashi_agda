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

## 7. October 27 sociology/philosophy source-owned max-cut continuation

**Implementation:** \`DASHI/Economics/WealthTaxPowerCareSociologyBidi20261027Exact.agda\`.
This new *application/consumer* imports pre-existing DASHI philosophy, sociology, governance, economics and query adequacy owners instead of creating a new universal philosophy/sociology ontology. The Economics \`Everything.agda\` aggregator registers it after the tax-base module, and a pre-existing escaped-literal \`\\nimport\` text splice in that aggregator was normalised to actual newlines. No changes are made to any of these upstream owners.

### 7.1 Reused formal and intellectual parents

- **Crenshaw/intersectional mathematical precedent:** \`DASHI/Core/IntersectionalNonFactorability.agda\` retains Kimberlé Crenshaw, *Mapping the Margins* (1991), DOI **10.2307/1229039**, as conceptual precedent. The loss-of-information theorem belongs to DASHI, *not* to Crenshaw.
- **Blackwell/query-indexed information:** \`DASHI/Core/QueryIndexedProjectionAdequacyExact.agda\`, David Blackwell's *Equivalent Comparisons of Experiments* (1953), DOI **10.1214/aoms/1177729032**, as information-comparison precedent, not a tax-effect theorem. The same assessed-tax observation is adequate for the tax-due query and inadequate for voting-rights/care-capacity queries.
- **Nancy Fraser's three axes:** \`DASHI/Governance/RecognitionDistributionRepresentationAxesExact.agda\` retains *Redistribution or Recognition?* (2003) and *Scales of Justice* (2009) as source context: redistribution, recognition and representation do not collapse. No one-axis verdict on 'justice' follows.
- **Nancy Fraser, \`Contradictions of Capital and Care\` (2016):** *New Left Review* 100, original HTML article, DOI **10.64590/nt2**, https://newleftreview.org/issues/ii100/articles/nancy-fraser-contradictions-of-capital-and-care. It argues social reproduction (care, households, maintenance of social relations) is a background condition of formal production, and financialised capitalist accumulation tends to erode that support. **The article does not say a specific billionaire tax rate solves the problem.** In fact, the original explicitly demands deeper structural transformation than tinkering with social policy; do not collapse it to 'tax to fund childcare'.
- **Silvia Federici, \`Wages Against Housework\` (1975):** first edition April 1975, original political pamphlet by Federici, published Power of Women Collective/Falling Wall Press (ISBN 0950270296). Bibliographic root https://books.google.com/books?id=6hzVAAAAIAAJ . Preserves an argument concerning unwaged housework and the political meaning of recognition/payment for domestic labour, not a statistical finding about effective top tax rates.
- **Sherry R. Arnstein, \`A Ladder of Citizen Participation\` (1969):** *Journal of the American Institute of Planners* 35(4), DOI **10.1080/01944366908977225**, publisher abstract https://doi.org/10.1080/01944366908977225. Distinguishes mere apparent participation from actual power to set/decide the programme. Already source-owned by \`DASHI/Culture/CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact.agda\`; new work does not claim she authored a corporate-vote theorem.
- **Patricia Hill Collins, \`Learning from the Outsider Within\` (1986):** *Social Problems* 33(6), DOI **10.2307/800672**, original publisher abstract https://doi.org/10.2307/800672. Primary sociological standpoint and interlocking oppression theory; does not assert marginality automatically makes empirical claims correct. Already included in the same Cohn/Ibrahim acquisition owner.
- **Historical sociology / Gramsci:** \`DASHI/Culture/HistoricalSocialTotalityBidiExact.agda\` already separates material, legal, cultural, institutional and historically situated subject positions; the finite theorem **same economic position does not recover unique ideology** remains owned upstream. The new tax consumer imports it verbatim.
- **Philosophy second-order power and intervention:** \`DASHI/Philosophy/PowerAndGrammar.agda\`, \`PhilosophicalPromotionBoundary.agda\`, \`MaterialFeedbackIntervention.agda\`, \`InhumanRelationalFork.agda\` distinguish rule-setting and epistemic admissibility, material feedback, and non-equivalent ethical consequences of a shared metaphoric premise. The 100% cap changes a tax rule but does not, *from that fact alone*, identify who controls the policy grammar or material redistribution.
- **Causal comparisons:** \`DASHI/Reasoning/ComparativeInstitutionalMeaningExact.agda\` already insists a regime label is not a matched counterfactual. Similarly, \`DASHI/Education/DigitalESDPoliticalEconomyProvisioningExact.agda\` owns differentiated ownership, revenue, provisioning, labour, externality allocation and participant decision power. Do not replace those precise coordinates with the blanket noun 'capitalism'.
- **Ibrahim social-science parent:** \`DASHI/Wikimedia/IbrahimEnglishSocialScienceFunnelBridgeExact.agda\` gives Sociology **Q21201**, Social science **Q34749** as *external navigation/coverage* coordinates. It explicitly treats sociology as *fragmented indirect coverage already present*, and adds only a parent seam; Wikipedia identity is not philosophical truth or source ownership. This local consumer does not promote historical First Link Network edges without the exact 2014 dump/producer/result chain.

### 7.2 Two exact finite information obstructions

Synthetic fiscal/social snapshots are:

\`\`\`text
World A: assessed wealth 5, controlling votes 1, accessible care 0
World B: assessed wealth 5, controlling votes 7, accessible care 0
World C: assessed wealth 5, controlling votes 1, accessible care 9
hard-cap threshold 3 -> tax due 2 in all three worlds
\`\`\`

- **A/B:** same assessed tax and same wealth, *different voting control*. INF non-factorability proves no function of *only that tax receipt* can recover both voting answers; any post-hoc recharting of the receipt also fails.
- **A/C:** same assessed tax and same wealth, *different care provisioning*. The receipt is likewise insufficient to determine realised care capacity.
- **Query-indexed adequacy:** the receipt **does** factor the 'what is the assessed tax?' query through the identity map, while simultaneously failing the power/care queries. This is a stronger constructive consumer than labelling a policy 'progressive'.
- **Interpretation limit:** these artificial worlds prove *information insufficiency relative to defined coordinates*, not that taxes cannot change votes, welfare or class power. Successful policy interventions might alter the hidden coordinates; their actual transition dynamics require measured source receipts.

### 7.3 Correct the philosophical claims in the supplied AI conversation

| Prior AI shortcut | Source-bounded correction |
|---|---|
| 'Anarchists all agree zero taxes and identical institutional policies' | SEP distinguishes socialist, communist, individualist and anarcho-capitalist traditions; shared critiques of state authority do NOT make property/ownership, free markets and solidarity compatible. https://plato.stanford.edu/entries/anarchism/ |
| 'Marx's tax plank is the endpoint' | *Manifesto* 1848 explicitly presents a group of transitional measures in a proposed programme; ownership changes and state power are part of the original context. Original https://www.marxists.org/archive/marx/works/1848/communist-manifesto/ch02.htm |
| 'Fraser/Federici prove a wealth ceiling funds and thereby repairs care' | Distinguish authorial theory about reproductive labour/social contradictions from a new policy-model counterfactual. Neither author proves that a specified marginal rate solves reproduction crises. |
| 'Top statutory rates explain the Great Compression' | WWII mobilisation, labour institutions, income definition, enforcement and asset response require matched causal decomposition. Do not infer treatment effect from joint history. |
| 'Techno-feudalism, postmodernism and accelerationism imply one unitary view of taxes' | Without author-specific original text and exact proposition, keep these as **candidate schools/interpretations**; do not canonise claims about what every adherent thinks. |
| 'Observed fall in Vancouver vacancies identifies policy-only effect' | Original city *2025 Annual Report* reports 2017–2024 drop and explicitly warns that isolation of the tax effect from population and housing-market causes is challenging. Source https://vancouver.ca/files/cov/2025-empty-homes-tax-annual-report.pdf |
| 'Most net wealth taxes were repealed, so no rational tax design could work' | Original OECD 2018 report argues taxation of wealth must be assessed in the context of the complete tax system; recommends treatment of trust structures, hard-to-value assets, debt deductions, instalments, foreign holdings and reporting. Source https://www.oecd.org/en/publications/the-role-and-design-of-net-wealth-taxes-in-the-oecd_9789264290303-en.html |

### 7.4 Max-cut / Pareto / Snowball acceptance ledger

| Priority | Paid or open | Completion condition |
|---|---|---|
| **P0** existing conceptual parents | PAID/reused | keep original author/year/DOI and upstream original module identities; avoid synonyms masquerading as new ontology |
| **P0** finite votes/care tax-receipt BIDI | SOURCE-WRITTEN | typecheck exact module; independent Python regression checks the sample worlds |
| **P0** syntax/reachability | SOURCE-WRITTEN | \`Everything.agda\` now imports both economic modules and its literal escaped import separators are repaired |
| **P1** social reproduction causal consumer | OPEN | care-hours/care-access outcome panel, differentiated by class, gender and labour type, plus a policy contrast and uncertainty |
| **P1** wealth ownership to vote power | OPEN | repeated person/company/entity beneficial ownership registry, share/voting rights, transfers, instruments, tax base and receipts |
| **P1** state institutional capacity | OPEN | legislation, collection/enforcement capacity, appeal/fairness and administrative cost (AI is a *tool*, not a constitutional authority) |
| **P2** Marx/Fraser/Federici BIDI against competing economic school models | PARTIAL | retain original text as authored position, expose falsifiers and different institutional proposals; do not assume one verdict |
| **P2** tax outcomes by population intersection | OPEN | measure distribution, representation, care and externalities separately; avoid using identity/standpoint as observed causal effect |
| **P3** historical period counterfactual | OPEN | 1946–1963 peacetime design with matched confounders and statutory-versus-effective definitions |
| **P3** cross-policy comparison | OPEN | modern city vacancy, estate, capital-income, net-wealth and proposed 100% stock cap have distinct units and evidentiary standing |
| **P4** full 2014 Ibrahim Wikipedia producer reproduction | OPEN but NOT this domain's blocker | retain existing \`IbrahimSnowballParetoFrontierExact\` rank-1 input/chunk/output provenance residual. Do not duplicate or assert its payment here |

### Status and provenance

This extension does not run a new tax study, infer a modern legal duty, prove anti-capitalist or pro-capitalist philosophy, or claim exact-read philosophical evidence automatically provides a political theorem. The new named proof terms and query witnesses are *source-written* unless and until the exact PR head is typechecked with Agda; the standalone Python tests are *executed computational checks* only. Earlier core proofs and historical source owners retain their distinct attribution.

## 8. Fiscal transmission, ownership power and assessment timing — max-cut round three (2026-10-27)

**New source-written owner:** \`DASHI/Economics/WealthTaxFiscalTransmissionControlBidi20261027Exact.agda\`.
**New runnable negative controls:** \`scripts/check_wealth_tax_maxcut.py\`.
**CI validation route:** existing \`.github/workflows/philosophy.yml\`, augmented with the source-file path filter and three Agda leaf checks plus the Python regression. No CI pass or typecheck asserted until an actual workflow run is examined.

### 8.1 Fiscal inference chain requires separate receipts

Formal state carries \`netWealthAssessed\`, \`taxPaidCash\`, \`collectionCostCash\`, \`appropriatedCareCash\`.

| Synthetic world | Assessed wealth | Tax due | Tax paid | Admin cost | Care appropriation |
|---|---:|---:|---:|---:|---:|
| Due/unpaid | 5 | 2 | 0 | 1 | 0 |
| Due/paid | 5 | 2 | 2 | 1 | 0 |
| Due/paid/allocated | 5 | 2 | 2 | 1 | 2 |
| Due/paid/high-cost | 5 | 2 | 2 | 3 | 0 |

*Same assessment -> different actual collection*: no function of liability **alone** can recover payment across these two worlds. Reuses \`INF.NonFactorabilityWitness\`, not a new information ontology. *Same collection -> different appropriation* and *same collection -> different collection cost* are independently witnessed. No artificial negative-net-revenue field is silently rounded to zero.

Crucially, this is a **non-determination**, not a prohibition of effective tax administration or a finding that taxes harm care. In the real world, payment probabilities, collection costs, budgeting institutions and service delivery must be measured.

### 8.2 Concrete dual-class share control discriminator

**Original primary regulator/standard-setting roots:**

- **Australian Securities and Investments Commission**, *Shareholder rights and responsibilities* (retrieved 27 October 2026), https://www.asic.gov.au/for-business-and-companies/companies/company-share-and-shareholder-rules-and-changes/shareholder-rights-and-responsibilities : different classes may have different voting rights; polling and resolution votes depend on company constitution and applicable law.
- **Australian Accounting Standards Board**, *AASB 10 Consolidated Financial Statements*, compiled 31 December 2024, https://www.legislation.gov.au/F2015L01617/2024-12-31/2024-12-31/text/original/epub/OEBPS/document_1/document_1.html : B6 describes the straightforward majority-votes case but B38–B39 clarify control from contracts and potentially less than majority votes. Accounting control is not identical to all legal ownership/beneficiary tests.
- **Singapore Exchange**, *Equity Securities Listing Rules*, Chapter 2, https://rulebook.qasgx.com/rulebook/chapter-2-equity-securities : dual-class listed shares may carry up to ten votes each, with specific conversion and governance constraints. This is an **example of a source-defined 10:1 mechanism**, not a rule automatically applicable to Australian companies.

**DASHI synthetic register (no named company):**

\`\`\`text
ordinary class total 20 (1 vote each)
super class total 3 (10 votes each)
total 50 voting units
founder initially 6 ordinary + all 3 super -> 6 + 30 = 36 / 50 = 72%
founder transfers all 6 ordinary units -> 0 + 30 = 30 / 50 = 60%
\`\`\`

The transferable block is deliberately ordinary and the hypothetical super-class untouched. This produces an **exact counterexample** to a rule 'transfer of a monetary/share block must mean loss of corporate voting majority'. However it proves **neither** that a specific proposed wealth tax would collect a fixed number of shares nor that a real founder must retain control. Transfer limitations, company constitution, proxies, share-class sunset/conversion, debt/control agreements and other law are case-specific consumer obligations. No claim of actual named-billonaires' ownership is made.

### 8.3 A 100% annual wealth tax above a threshold is not a *continuous* wealth cap

For hypothetical threshold 3 and assessed wealth 5, levy 2, post-assessment stock 3. Subsequent intra-year growth of 2 yields stock 5 **until the next assessment**, where the illustrative policy collects 2 again. Two equalities are checked independently: the assessment can set the stock to 3 on the date; the stock can exceed 3 between dates.

This is neither a constitutional impossibility nor a claim that annual taxation is ineffectual. It separates the **stock cap on assessment date** from a **continuous legal ceiling** and highlights asset valuation frequency, mark-to-market accounting and response timing as explicit design axes.

### 8.4 Additional philosophy/sociology consequences

- Fraser's *Contradictions of Capital and Care* (2016) explicitly analyses the gendered, classed and geographically displaced reproduction crisis and exclusionary postwar arrangements. A high tax **plus care earmarking** is one possible policy mechanism to investigate, not sufficient proof of universal care justice. Cite original https://newleftreview.org/issues/ii100/articles/nancy-fraser-contradictions-of-capital-and-care .
- Arnstein's citizen-participation distinction asks who makes allocation decisions, rather than treating the nominal appropriation amount as a certificate of democratic participation. Existing primary owner remains \`CohnInstitutionalIbrahimDeweyAcquisitionExtensionThreeExact\`.
- \`PowerAndGrammar\` asks who sets the tax base, liability exceptions, spending priorities, audit burden and appellate evidentiary grammar. The new numbers do not automatically answer this second-order political question; the answer requires institutional data.
- \`HistoricalSocialTotalityBidiExact\` prohibits class position -> uniquely recovered ideology. Proposed tax design is not a classification of all members of any economic or political class.
- The shared Ibrahim Wikipedia social-science funnel is **navigation only**, not a factual proof of any of these authors' doctrines or economic outcomes.

### 8.5 Latest PR method transfer and stopping wall

Observed GitHub current relevant PRs: #1275 source-typed Zipf family and strict law-vs-observation distinction, #1276 Woogaroo same-object source/authority and beneficiary nonpromotion, #1267 severe paired hypothesis tests, #1245 original-root evidence chain. None is an empirical sponsor or proof owner for this tax problem; no edits were made to their branches.

**P0 newly paid as SOURCE-WRITTEN:** exact finite payment/appropriation/cost/dual-vote/inter-assessment models; test code and CI coverage route. **P1 NOT paid:** real collection rates, audited administration cost, multi-jurisdictional beneficial-ownership time series, firm voting-control rights after actual tax-motivated transfers, appropriation/disbursement/service access and matched counterfactuals. **P2 NOT paid:** a causal macro comparison of the proposed 100% ceiling, which is not enacted policy; tax incidence and realistic response equilibria require assumptions and data. **Agda kernel status:** unverified in this session. **Sociology status:** original historical theory appropriately source-bounded.

**Expected highest-value next consumer:** one linked identity- and time-indexed graph containing (a) original legal tax instrument, base/jurisdiction/rate, (b) assessed asset and owner, (c) realised payment/appeal, (d) voting instrument and control agreements, (e) appropriation, expenditure and effective care outcome, (f) the contrasted population/time/control. Absence of that empirical graph is an actual wall: constructing more synthetic snapshots does not resolve causation.

## 9. Requested-topic inventory and exact status (27 Oct 2026)

**All 42 subjects in both user-supplied transcripts** now have an explicit ID, claim-strength category, underlying root or unfilled source obligation, and bounded counterargument in the adjacent audit:

[WealthTaxOriginalConversationsFullCoverage20261027.md](WealthTaxOriginalConversationsFullCoverage20261027.md).

An executable structural completeness check lives at \`scripts/check_wealth_tax_requested_topics.py\`, registered in the existing philosophy/economics workflow. Its receipt only proves inventory presence and source/claim-ceiling text; it **does not certify original research, facts, Agda theorem verification or causal predictions**.

### Three particularly consequential corrections

1. **Adam Smith versus vacancy taxes.** *Wealth of Nations* (1776), Book V, Chapter II, Part II identifies rent, profits and wages as distinct income categories, discusses ground-rent taxation, and argues uninhabited houses should not incur the cited house-rent tax. That is a primary historical normative view, not a proof that current Vancouver/Victoria vacancy schemes fail or are unjustified. Transcribed root: https://en.wikisource.org/wiki/The_Wealth_of_Nations/Book_V/Chapter_2 . Separate modern statutory taxable object from eighteenth-century house-rent category.
2. **Curtis Yarvin's Patchwork** (13 Nov 2008) explicitly suggests a self-assessed property tax for corporate-sovereign realms. This falsifies any blanket attribution that Yarvin's *own particular proposed design* contains no taxation. It does **not** justify Yarvin's political preferences or conflate him with anarcho-capitalism. Primary authored root: https://www.unqualified-reservations.org/2008/11/patchwork-positive-vision-part-1/ .
3. **Thomas Piketty** clarifies in his own 2015 *JEP* article (DOI 10.1257/jep.29.1.67) that \`r > g\` is neither the only nor primary factor for every wealth inequality trend, so it is **not** an absolute mathematical inevitability proof. This is an authorial original, not a generic paper replacing an original citation.

**Previously omitted instruments/source roles:** OECD Pillar Two corporate GloBE profit top-up (not personal wealth), HMRC share stamp duty (normally 0.5%, not a universal 0.1% FTT), FATF beneficial-ownership reporting (competent-authority access rather than universal public data), Henry George's site-value/rent tax, and 2013 left versus 1994/1997 Landian versus 2022 e/acc accelerationist author groups. The new receipts are in the existing two economics application modules, not in new discipline owners.

**Quality status:** 42 rows inventoried and checked structurally in an exact GitHub blob; original/source/claim-ceiling audit remains a reading document. Full empirical settlement is limited by 10 open-evidence subjects after paying the Smith passage, including shifting billionaire valuation, FDR causality, AI audit performance, Samsung control, France mobility/administration data, algorithmic harassment tax effects and blackpill/doomerism author-specific claims. Open is not "missing topic"; it means **the relevant claimed effect has no admissible same-object proof receipt**.

## 10. Pareto snowball 2026: social protection, portfolio adjustment and TOE reachability

**Newest dated original-source roots, inspected 27 October 2026:**

- **OECD (9 September 2026)**, *Financing of Social Protection*, Chapter 3 "Securing the Revenue Base for Social Protection", DOI **10.1787/b384fd31-en**. Primary institutional report: https://www.oecd.org/en/publications/financing-of-social-protection_b384fd31-en/full-report/securing-the-revenue-base-for-social-protection_fee691c9.html . OECD's unweighted 2024 table gives recurrent net wealth taxes **0.4%**, estate/inheritance/gift taxes **0.4%**, and financial/capital-transaction taxes **1.2%** of OECD government revenue. These are **different historical bases and observed revenue shares**. The report discusses population ageing, potential AI-driven labour/capital share changes, tax-design trade-offs and diversified social-protection financing. It does **not** assert observed mass AI job loss or provide a causal forecast of a hypothetical 100%-above-threshold wealth policy. Relative to Fraser/Federici, OECD's social-protection categories provide an *administrative funding panel*, not a full measure of unpaid reproductive labour or democratic control.
- **Andreas Fagereng, Luigi Guiso and Marius A. K. Ring (May 2026)**, NBER Working Paper **35262**, DOI **10.3386/w35262**, https://www.nber.org/papers/w35262 , is a *working paper*, not a magically peer-reviewed proof. It describes strong but slow Norwegian investors' portfolio adjustments to persistent wealth-tax-induced equity-premium changes, distinguishing short- and long-run response. It is a **second mechanism class** next to Jakobsen et al. (2026) cross-border migration. Do not conflate migration, portfolio entry/rebalancing and aggregate growth as one datum.
- **Moustafa Chatzouz (14 August 2026)**, IMF Working Paper *Public Debt, Wealth Inequality, and the Burden of Taxation*, DOI **10.5089/9798229055925.001**, https://www.imf.org/en/publications/wp/issues/2026/08/14/public-debt-wealth-inequality-and-the-burden-of-taxation-578868 : author-owned overlapping-generations model with debt/tax-burden/inequality regime shifts and cross-country empirical support. Conditional model dynamics are not a theorem that all debt raises inequality, and the author's argument is not an institutional IMF endorsement of a wealth tax.
- **European Commission DG TAXUD, CASE, WIFO, PwC, IEB, ifo, VATT, Andrzej Robaszewski and co-authors (15 April 2026)**, *Wealth taxation, including net wealth, capital and exit taxes*, Volume I, DOI **10.2778/0817231**, https://op.europa.eu/en/publication-detail/-/publication/b3294f0c-386f-11f1-be39-01aa75ed71a1/language-en : comparative source for **multiple nonidentical** bases and implementation constraints. Group authorship and individual authorship remain separate from DASHI's source-written model.
- **FATF (10 March 2023)**, original *Guidance on Beneficial Ownership of Legal Persons* / Recommendation 24, https://www.fatf-gafi.org/en/publications/Fatfrecommendations/Guidance-Beneficial-Ownership-Legal-Persons.html . FATF **Recommendation 25 for trusts and legal arrangements** has separate **11 March 2024** guidance https://www.fatf-gafi.org/en/publications/Fatfrecommendations/Guidance-Beneficial-Ownership-Transparency-Legal-Arrangements.html . These legal objects and years must not be treated as one globally complete universal wealth registry.

### 10.1 Attribution and independence

**Original theory** Marx/Engels 1848; Piketty 2015; Fraser, Collins, Arnstein, Federici; distinct philosophical schools retain original dated authors. **Original public observations** OECD 2026 2024 revenue table; US FRED historical statutory series; Vancouver 2025 municipal report; Victoria SRO; each is a producer, not independent confirmations through downstream journalism. **Separate academic methods** NBER 2026 investor panel, AER 2026 rich-taxpayer migration, IMF 2026 structural modelling and EU 2026 comparative report do not become interchangeable empirical replications. **DASHI finite Agda source** models exact counterexamples; the separate numerical regression (Python) is computational only; **Agda kernel** remains not witnessed. **Ibrahim historical 2014 FLN/2017 paper** supplies knowledge-graph navigation only. QID or rank similarity does not prove a social-science theorem or same-object Monster representation. No ESD surfaces are edited.

### 10.2 Canonical TOE import-graph max-cut

The 27 October snapshot shows a **large branch/master divergence in the canonical specialised TOE roots**: the feature branch still has a small \`DASHI/EverythingTOESymmetryResolved369.agda\`, \`DASHI/Unifier.agda\` and \`DASHI/Unified/Everything.agda\`, whereas current master includes much larger and later Fleet, Balaban and Ibrahim convergence. **Do not replace any of those newer roots with the feature branch's older version merely to add an economics import.** An otherwise harmless edit would risk superseding later attribution and proof status. The PR remains mergeable because the three roots have not been modified.

Safe root verified **byte-identical** on feature branch and live master before edit: \`DASHI/Everything.agda\`.

- New **thin consumer** \`DASHI/Unified/WealthTaxEvidenceNonPromotionTOEExact.agda\` imports the three source-owned Economics modules plus pre-existing generic \`IntersectionalNonFactorability\`. It exports explicit aliases for stock ≠ income, GloBE ≠ personal stock tax, assessed liability ≠ payment, payment ≠ care appropriation, assessed stock ≠ political voting control, tax receipt ≠ care delivered, audit score ≠ legal tax, and finite model ≠ causal policy evidence.
- The consumer is **registered directly through the safe canonical \`DASHI/Everything.agda\` import graph**. Existing owners keep all proof authorship; no general-purpose sociology or political-theory ontology is created.
- CI \`.github/workflows/philosophy.yml\` now includes the new bridge and root as workflow-path triggers. It runs Python bounded arithmetic, the 42-topic structural inventory, \`dashi-agda-preflight\` on all three economics modules and the bridge, Agda leaf typechecks, then prior philosophy regression and the repository's aggregate philosophy checks.
- The **three specialist TOE root aliases** remain a *separate post-merge integration task on current master* because writing whole old source files over them would be destructive. Reachability from \`DASHI/Everything.agda\` is not a claim that the modern specialized \`Unifier\` or \`EverythingTOESymmetryResolved369\` files now export this consumer, nor a claim that source-written proofs have passed compilation.

### 10.3 Explicit unresolved stop conditions

1. **Kernel**: exact-head preflight/typecheck and executed GitHub Actions CI must be observed. The local environment lacks an Agda binary and full original source worktree. The action steps are written but no run receipt is claimed.
2. **Empirical causal**: obtain same-person, same-company, time-indexed beneficial owner/voting instruments, valuation, liability, appeals, actual collection, public appropriation and realised care outcome. Comparison must distinguish migration, asset portfolio allocation, administration, re-investment and social reproduction, rather than conditioning only on nominal tax.
3. **Source genealogy**: original dated source authority and type of claim remain separate. A government guidance page is not necessarily an enacted national law, an NBER/IMF working paper is not an official consensus, and citations/secondary commentary are not a substitute for matching study populations.

**The economic-policy proposal is not implemented or empirically validated by these imports.** This is the Pareto frontier after completing the named tax/philosophy/sociology inventory and core finite countermodels.

## 11. Direct pasted-source max-cut correction: hypothetical "idle equity" and philosophy name roots

This pass re-inspected the two **user-supplied original pasted conversations**, rather than assuming the 42 topic-label inventory alone captured every subclaim. This paid a previously under-specified subclaim:

- The pasted AI proposes a separate **1%, 2%, 5%** annual escalating levy on stock blocks classified as "idle" in years one, two, and three or later. That schedule has **no supplied enacted law**, no verified legal definition of idle corporate equity, no approved valuation, no incidence research and no jurisdiction. It must not inherit Victorian vacancy-tax authority by analogy.
- Ordinary Victoria vacant residential land tax (VRLT) has its own **1%, 2%, 3%** year-dependent schedule, exemptions and residential land base. Neither instrument equals a net-wealth hard cap. The shared first two percentages are merely coincident numerical values.
- New \`TaxBase.unverifiedIdleCorporateEquityStatus\`, \`Policy.proposedDurationEscalatingIdleEquityLevy\`, and \`ProposalTenure\` rate-basis-point definitions in \`DASHI/Economics/WealthInheritanceVacancyTaxMaxCut20261027Exact.agda\` store the precise *hypothesis* without manufacturing a law. The 100/200/500 basis-point outputs deliberately remain rates only; multiplying by a defined taxable assessment or claiming revenue would require a separately verified statutory and measurement carrier. New non-equality proof blocks identity with the enacted vacant-homes policy. The TOE consumer reuses those proofs.
- \`scripts/check_wealth_tax_maxcut.py\` adds a finite schedule regression; \`scripts/check_wealth_tax_requested_topics.py\` fails if the proposal, actual VRLT discriminator, or source roots disappear from the topical audit.
- The philosophy transcript specifically names **bell hooks**, **Jean Baudrillard** and **Peter Kropotkin**. Their dated original roots were absent from the formal receipt list, even though their schools appeared in general topical prose. They are now preserved individually: bell hooks, *Feminism Is for Everybody: Passionate Politics* (2000; original author Gloria Jean Watkins; publisher Pluto edition), Jean Baudrillard, *Simulacres et simulation* (Éditions Galilée, 1981; [BnF catalogue](https://catalogue.bnf.fr/ark:/12148/cb34681600h)), Kropotkin, *The Conquest of Bread* (1892; [full original text](https://www.marxists.org/reference/archive/kropotkin-peter/1892/bread.htm)). They are original authors of philosophical positions, NOT of any formal Agda non-factorability proof or wealth-tax effectiveness estimate.

**Bounded interpretation:** The direct pasted texts are observations of earlier assistant responses, not authoritative historians or lawmakers. The new code demonstrates precise *nonidentity* and source attribution, not enactment, empirical causation, or ideological universality. The existing T17, T30, T32 and T39 inventory rows are expanded without treating additional detail as four new mathematical theorems. No unrelated PR or ESD module is modified.

## 12. Attribution-source proof reuse: citation, independence and result authority (28 October 2026)

**Owner quotient, not a new source ontology.** The thin TOE consumer `DASHI/Unified/WealthTaxEvidenceNonPromotionTOEExact.agda` now imports four pre-existing sources of proof obligations without modifying their owners:

1. `DASHI.Core.AttributedSourceCore` supplies `citationImportsProofIsFalse` and `citationCreatesAuthorityIsFalse`. The consumer explicitly aliases both for **every** inhabitant of the existing `AttributedSource` type. Named bibliography entries therefore remain attribution metadata and do not themselves import mathematical, statistical or legal authority.
2. `DASHI.Core.SnowballAttributionProvenanceInvariantExact` supplies `citationDoesNotCreateProof` and already tracks author, year, DOI, publication, access carrier, source type, formalisation role, visibility and non-promotion as separate relevance axes. It does **not** make a bibliography into an independent proof.
3. `DASHI.Core.EvidenceHyperfabricExact` supplies the proof that `independent` and `sharedLineage` are different source relations. The September OECD report, its chapter 3 on wealth-taxation revenue, and press articles derived from the same chapter are **one report producer/lineage**, not additional studies that corroborate one another. This use of the existing theorem is a source-lineage statement, not a universal source-independence classifier.
4. `DASHI.Economics.SourceAttributionPromotionBoundaryExact` already rules out promoting identical text into independent verification, a source assertion into systemic classification, or a source-use receipt into a promotion-step producer. These are directly re-exported instead of creating economics-local duplicates.

The local [42-topic audit](WealthTaxOriginalConversationsFullCoverage20261027.md) and `scripts/check_wealth_tax_requested_topics.py` now require the direct imported owners, named proof aliases, and a source bridge with no new `postulate` or `TERMINATING` shortcuts. They check that the proof-**source text** remains present. **This is not the same as checking those expressions in the Agda kernel.**

### 12.1 Severe source-first comparisons, without false independence

| Hypothesis | Admitted original root | Required test | False promotion rejected |
|---|---|---|---|
| Taxation raises money for care | OECD `Financing of Social Protection` (9 Sep 2026); its administrative funding accounts | Match enacted tax object, actual collection, net admin cost, funded services, population access and time | `assessed liability = realised care` |
| Investors adapt to wealth taxation | Fagereng, Guiso and Ring, NBER WP 35262 (May 2026) | Portfolio composition, investment horizon and identification, **not** taxpayer migration alone | `portfolio reallocation = economy-wide collapse` |
| Rich taxpayers change legal residence | Jakobsen, Kleven, Kolsrud, Landais and Munoz, `AER` 116(10) (Oct 2026) | Residence/wealth thresholds, years, destination, macro contribution and extrapolation | `migration = all-tax invalidity` |
| A hard cap breaks firm control | ASIC corporate share classes, AASB 10 contractual control standard, and company-specific voting instruments | Actual beneficiary registry, share classes, voting agreements, threshold, tax payment and after-transfer majority | `assessed wealth reduction = transferred control` |
| A fiscal rule changes who decides | Nancy Fraser 2003/2009, Sherry Arnstein 1969, Patricia Hill Collins 1986, plus institution-specific primary decisions | Observed redistribution, recognition and representation independently; compare policy governance | `progressive tax rate = democratic self-rule` |
| A distribution is inevitable | Thomas Piketty 2015 clarification; separately PR #1275 Zipf/Pareto source-typed models | Calibrated dynamics of growth, returns, shocks, gifts, institutions and regression tests | `r > g` or 80/20 fit `= physical inevitability` |

These are **alternative causal/mechanism tests**, not six statistics independent of their original producers. In particular the 2026 NBER Norwegian portfolio paper and 2026 AER Scandinavian migration paper ask different outcome questions even though they concern overlapping policy mechanisms.

### 12.2 Latest PR cross-pollination and exact stopping gate

PR [#1406](https://github.com/chboishabba/dashi_agda/pull/1406) reuses existing mathematics for a 2026 non-Archimedean paper; PR [#1405](https://github.com/chboishabba/dashi_agda/pull/1405) uses original-source ownership and query-indexed philosophy claims; PR [#1404](https://github.com/chboishabba/dashi_agda/pull/1404) separates test protocols from empirical receipts; PR [#1396](https://github.com/chboishabba/dashi_agda/pull/1396) brings existing `EvidenceHyperfabricExact` non-promotion into specialised TOE roots. Only **the method of source reuse** is transferred here. No sound-wave experiment, non-Archimedean spectral theorem, Monster 3B character or Kozyrev patent is a source for economic causation.

**Stop conditions:** GitHub Actions must actually run the relevant Python script, semantic preflight and Agda; the proof-source path must typecheck against the exact PR head. Current branch still does not modify the newer specialised TOE roots because their current master versions contain extensive independent work absent from the older branch snapshot. Attribution, empirical test data and kernel certification remain separate obligations.

## 13. Tax × dashiTRADE market / material max-cut (2026-10-28)

The direct user-requested cross-repo check inspected both the Agda trading proof owners and the independent [standalone private dashiTRADE](https://github.com/chboishabba/dashiTRADE). Both are part of the continuation scope.

### Reuse rather than re-prove

Existing Agda original repository owners are:
- DASHI.Finance.DashiTradeFibreBridgeExact: factor/residual proposal is not execution permission.
- DASHI.Trading.DashiTradeDreamOptionConeExact: equal direction can have different BUY availability; HOLD remains first class; trajectory cost is not endpoint value.
- DASHI.Economics.DashiTradeAIInfrastructureMarketCrossPollinationExact: identical demand signals do not identify refinancing viability.
- DASHI.Trading.TradingDeclaredRealizedViabilityBridgeExact: planned viability is not realised outcome.
- DASHI.Core.IntersectionalNonFactorability: generic formal non-factorisation belongs to this existing mathematical module; original Crenshaw 1991 owns conceptual priority, not Agda code or theorem verification.

This branch now has the distinct application DASHI.Economics.WealthTaxDashiTradeMarketMaterialBidiExact. It combines EXISTING inherited fiscal/market/finance fibres in three synthetic cases to demonstrate:
1. Identical assessed hypothetical wealth-tax liability **does not determine** BUY permission.
2. Identical infrastructure-demand signal **does not determine** refinancing availability.
3. Identical market-direction proposal **does not determine** public tax cash collection.
4. HOLD remains available in the inherited finite trading example.

These source-written Agda proof terms are not certified until an observed exact-head Agda run succeeds. Nothing grants trading authorisation or predicts measured financial/physical outcomes.

The new adapter is registered in Economics/Everything and re-exported through Unified/WealthTaxEvidenceNonPromotionTOEExact. The general canonical Everything import still reaches it; the three divergent specialist TOE roots remain untouched to protect more recent master branches and Ibrahim/Balaban/Fleet ownership. CI and the 42-topic topic-presence guard now require this Agda application and its inherited owners.

### Standalone Python lane, no runtime changes

A new [dashiTRADE PR #3](https://github.com/chboishabba/dashiTRADE/pull/3) carries:
- policy/wealth_tax_shadow.py: immutable, source/time-indexed, exact decimal fiscal shadow receipt; assessed tax liability, actual cash collected, collection costs, care appropriation, delivered care hours and share-class voting rights stay separate.
- tests/test_wealth_tax_shadow.py: eight synthetic negative controls, including pairing with the existing ShadowPolicyStep logging output without changing the live Intent.
- docs/wealth_tax_shadow_material_maxcut.md and a path-scoped GitHub Actions Python unittest gate.

Production run_trader, Nashi, broker, futures controller, intent.py and bar_exec.py are not modified. The independent [dashiTRADE PR #1](https://github.com/chboishabba/dashiTRADE/pull/1) (source-bounded AI capital financing) and [PR #2](https://github.com/chboishabba/dashiTRADE/pull/2) (TimesFM shadow) are unmerged; neither is imported or assumed installed.

### Attribution and physical implications

A wealth valuation is a market/legal claim, not a machine, power station or care hour. Even an enforceable cash tax liability must pass through collection, liquidity, possible portfolio transactions, company votes, financing/refinancing, public budgets and labour/capital capacity before changing real outcomes. Each transfer requires its own same-actor time-series and counterfactual evidence. The hypothetical 100% assessment-day threshold is **not** an enacted tax nor a market prediction.

Original independent roots: OECD *Financing of Social Protection* (9 Sep 2026, DOI 10.1787/b384fd31-en), Fagereng/Guiso/Ring NBER WP 35262 (May 2026, DOI 10.3386/w35262), and Jakobsen et al. AER 2026 immigration evidence. These sources concern distinct populations and outcomes and are not replications of a 100% stock wealth ceiling. Earlier philosophers, social scientists and official datasets retain their original source ownership; the resulting new product-world proof structure is DASHI repository work, not theirs.

### Remaining gates

P0: 42/42 requested source topics classified. P1: new Agda cross-domain source and shadow-only Python suite written, but exact-head Agda and GitHub CI run must be observed. P2: obtain same-object ownership, legal assessment, tax receipts, actual trades/refinancing, physical construction/worker-hour data; still open. P3: competing-policy causal/negative-control tests; still open. P4: selectively integrate into current-master specialist TOE roots and preserve Ibrahim first-link history and Monster 3B proof ownership; still open.

**No policy authorisation, live trading, measured capacity, scientific discovery or economic causal validation is inferred from the synthetic examples.**

## 14. Pareto/snowball increment: how tax receipts are financed and resources are produced

The cross-repository tax/dashiTRADE owner is extended **in place**, not cloned into a new source ontology. The new Agda application FundingRoute explicitly supplies cash resources, newly borrowed funds, gross asset-sale proceeds, share counts, execution costs, and installed physical production units.

For every synthetic funding fixture it requires the exact equality:

    unrestricted_cash + new_loan_cash + gross_asset_sale_cash
      = tax_cash_collected + execution_cost_cash

Five Agda world fixtures reuse the same paid hypothetical tax but select different cash, loan, sale, execution-cost, and machine-capacity coordinates. Generic IntersectionalNonFactorability supplies three source-owned theorem applications:

- paidTaxCannotDetermineUnitsSold: two worlds collect identical cash yet report zero versus two share units sold.
- saleVolumeCannotDetermineExecutionCost: two worlds sell the same number of shares but incur distinct costs.
- saleVolumeCannotDeterminePhysicalCapacity: two worlds sell two shares but carry different externally specified installed-machine stocks.

The thin TOE consumer now re-exports these **existing-owner-based** negative results. This eliminates the unwarranted policy-chain inference from assessed liability to automatic forced sale, price impact or actual construction. A bounded accounting equality is not sufficient to infer borrowing capacity, actual sale volume, market-clearing prices, corporate control, or physical output. The model does not include market equilibrium, and these are not causal empirical statements.

The standalone [dashiTRADE PR #3](https://github.com/chboishabba/dashiTRADE/pull/3) mirrors the same distinction with an immutable PaymentFundingRoute, strict exact-decimal input checks, a balance requirement and synthetic fixture tests. The new code is shadow-only and does not modify intent, execution, live controls or order routing.

### Severe independent-original-source discrimination

1. [Fagereng, Guiso and Ring, NBER WP 35262 (May 2026)](https://www.nber.org/papers/w35262) study slow portfolio allocation changes and different participation margins after actual Norway wealth-tax-induced equity-premium shifts. This does not imply every payment is funded by forced liquidations.
2. [Minsoo Kim, Fund Flows, Liquidity, and Asset Prices, Management Science (11 June 2026), DOI 10.1287/mnsc.2025.01690](https://doi.org/10.1287/mnsc.2025.01690) studies forced selling **by bond mutual funds experiencing redemption shocks**, and bond liquidity. It provides a credible microstructure mechanism, not a measured effect of a personal wealth-tax ceiling or a validation of a dashiTRADE fill model.
3. [Francesco Bianchi, Nicolò Ceneri, Leonardo Melosi and Alessandro T. Villa, Fiscal Policy and the Saving Glut of the Rich, NBER WP 35715 (September 2026)](https://www.nber.org/papers/w35715) study debt- versus inflation-financed transfers and wealth distribution through a structural macroeconomic model. It motivates separating **who holds new debt** from nominal spending and asset valuation, not an automatic welfare or market-price forecast.
4. [OECD, Financing of Social Protection (9 September 2026)](https://doi.org/10.1787/b384fd31-en) records social-protection finance instruments and their different administrative/behavioural distortions. Collected money is not directly a quantified care-hour outcome.

There is no source-independent observed estimate here of a hypothetical 100% annual billionaire ceiling. Repeated original-paper abstracts, provider page mirrors and code comments remain the same source lineage. Existing Ibrahim first-link navigation, Pareto/Zipf prior theorem owners and Monster 3B same-object constraints are not converted to finance experiments. Previous Crenshaw, Fraser, Marx, Georgist and feminist original authorship is preserved.

The exact source-written implementation and independently specified negative controls are a **finite algebraic model**, not a physically measured system. The next frontier is an executed same-actor, same-date cash/borrowing/security-sale trace, institutional control documentation, and separate installation/workforce service-outcome measurements.

## 15. Exact same-object share-class reconciliation, not merely sale volume

A newly discovered gap after the funding-route max-cut was **unit identity**: a seller may sell two ordinary shares or two super-voting shares. Equal asset-sale volumes are not equal legal/control changes. Also the earlier synthetic 6-ordinary-share transfer cannot automatically be welded to a separate two-unit sale receipt. Treating the two as one observation without reconciliation would violate the user attribution and same-object rules.

The existing Agda tax–market owner now adds an optional FundingVoteReconciliation. A proof-bearing link contains the funding route, before/after voting ledgers, separately counted ordinary/super-voting transfers, a transfer-unit count equal to the route's sale count, exact owner holdings reconciliation for both classes, and unchanged total issued shares and class voting conditions in this finite example.

Two explicit same-count examples (not observations of a company):
- Starting owner: 6 ordinary + 3 super-voting shares, ten votes per super, with 20 ordinary and 3 super shares outstanding (owner votes 36 of 50).
- Ordinary-class two-unit transfer: owner retains 4 ordinary + 3 super, hence **34/50** owner votes.
- Super-voting two-unit transfer: owner retains 6 ordinary + 1 super, hence **16/50** owner votes.

Both use the same paid hypothetical tax, same gross fixture sale cash, same share count sold and same execution-cost fixture. The inherited IntersectionalNonFactorability core therefore rejects a universal reconstruction of the owner's weighted voting rights from an aggregate sale-count projection. The theorem is a DASHI synthetic finite model, not a result attributed to tax scholars or proof of legal control in any listed company. Voting agreements, reserved matters, directors' duties, shareholder classes and effective beneficial ownership still require company-specific actual primary documents.

The thin TOE consumer now exports toeShareSaleCountDoesNotFixWeightedVoting and the topic guard checks the original owner and constructor. No new general factorisation library, ESD edit or specialist TOE-root overwrite was added.

The standalone [dashiTRADE PR #3](https://github.com/chboishabba/dashiTRADE/pull/3) now adds ShareClassSaleLink. This checks an existing shadow FundingRoute against explicit owner before/after ordinary and super-voting units. An old fixture in which **six** ordinary units transferred cannot be silently joined to a route selling **two** shares. That invalid join is rejected. Exact-blob reconstructed Python tests (the new shadow and tests, plus the unchanged original shadow runner) now pass **16/16** isolated cases, including negative matching tests. This is an executed Python receipt only; it is not an Agda kernel pass, a real audit of an issuer register or a tax-policy empirical result.

The strongest physical implication remains conditional: ownership, legal voting control, debt funding, execution costs and productive plant stock are distinct. Financial tax payment and legal share settlement can occur without any construction or destruction of machines, while control may change depending on the precise transferred rights. Without external same-actor/time matched data, no estimate of actual output, employment, energy, caregiving or price change is licensed.

Original sources: ASIC shareholder-rights rules, AASB 10 accounting control rules, and SGX dual-class listing rules retain their own jurisdiction-specific authority and dates, cited separately above. New financial study mechanisms (Fagereng/Guiso/Ring 2026, Kim 2026, Bianchi et al. 2026) retain their original authors and independent populations. No numeric coincidence, Ibrahim knowledge-graph link or Monster 3B analogy manufactures company-control proof.

## 16. Cash settlement and temporal provenance (28 October 2026)

After the earlier paid-tax-versus-sale-volume and share-class max-cuts, an exact same-object weakness remained: a gross asset-sale amount and two share units were present without a witnessed breakdown of orders, individual fills, unit prices and **cash settlement**. The original fixture sold two units for gross proceeds three. Its construction did not imply a single uniform whole-number price.

The **existing** WealthTaxDashiTradeMarketMaterialBidiExact Agda owner now adds an optional TwoFillSettlementLink. It requires:
- intended order volume = two executed fill volumes + unfilled remainder;
- each executed fill = settled quantity + unsettled remainder;
- settled share quantity = the already-balanced funding route's sold unit count;
- gross settled proceeds = sum of the two settled-unit counts times their independently stated unit prices.

Two bounded worlds have *identical two-unit submitted orders*: submittedWithoutFill settles zero shares and uses available cash, whereas twoPricesThreeProceeds settles two distinct one-unit fills at prices 1 and 2, producing gross proceeds 3. An executedUnsettled world has two executed but **zero settled** units. These are two reused INF nonfactorability cases: submittedOrderDoesNotDetermineSettlement and executionDoesNotDetermineSettlement. They do not create broker authority or general price impact.

A separate MatchedSettlementTaxChronology structure requires an explicit nonnegative forward lag between the separately observed final sale-settlement epoch and tax cash-collection epoch. The source-written finite contradiction priorCashReceiptHasNoForwardSettlementLink rejects modelling a tax payment at epoch 1 as funded directly by settled cash arriving at epoch 3, **unless an independently sourced alternative funding route is specified**. The epochs are model counters, not automatically venue business days or historical transaction data. The positive accounting statement twoFillCashConservation remains conditional on the stated finite fill receipts.

The existing TOE consumer now re-exports these source-owned examples; the 42-topic guard requires the named owner symbols. The new Agda text has **not been typechecked with an Agda kernel** in this environment. The latest exact GitHub trade adapter and tests have been reproduced locally with **26/26 passing isolated Python tests**, not a live order or a tax authority record.

Original independently dated institutional authorities distinguish the jurisdictions:

- [ASX Clearing and Settlement / CHESS](https://www.asx.com.au/markets/clearing-and-settlement-services/asx-settlement): Australian cash-equity T+2 settlement and delivery versus payment. Registered title and cash move together when CHESS settles; this does not set an observed rate for a specific share.
- [SEC T+1 final rule (15 February 2023)](https://www.sec.gov/rules-regulations/2023/02/34-96930) and [May 2024 implementation](https://www.sec.gov/newsroom/press-releases/2024-62): US standard shorter-cycle settlement since 28 May 2024, not the same Australian settlement service.
- [ASIC, Shareholder rights and responsibilities](https://www.asic.gov.au/for-business-and-companies/companies/company-share-and-shareholder-rules-and-changes/shareholder-rights-and-responsibilities): share classes, constitutions and meeting-vote rules remain separate from price or count alone.
- [Fagereng/Guiso/Ring (May 2026)](https://www.nber.org/papers/w35262): slow Norwegian investor portfolio adjustments after a tax-induced equity premium shock, not a timed forced-sale tax settlement or a 100% cap experiment.

**Physical implication and current wall:** The hard step is not a further theorem about order IDs. It is obtaining *same-actor, same-instrument, same-jurisdiction, event-time-matched* taxation and custody documents that connect valuation, assessment, cleared funding, ownership-right transfer and downstream physical service or capital production. Source-written finite receipts are a method for checking such a join, not substitutes for its source data. Historical intellectual original authors, independent DASHI proof authors, standalone dashiTRADE runtime authors, and previously owned Ibrahim Monster 3B results remain separate attribution classes. No ESD module or specialist TOE root is modified.

## 17. Instrument-identity max-cut: class count is not a trade identity

The settlement round uncovered a second false join: the same two-unit sale may consist of ordinary shares or super-voting shares. Neither the quantity, fill price, monetary settlement nor order time establishes the rights of a particular class. An earlier six-share synthetic transfer is not the same transaction as the later two-unit funded-sale fixture without a matching instrument/ownership chain.

The existing Economics/dashiTRADE Agda application now defines SettlementInstrumentClass and IdentifiedClassSettlement. The constructor explicitly retains issuer and instrument source labels, class, and a class-compatible transfer witness. The generic, previously owned INF theorem is reused in saleVolumeCannotIdentifyInstrumentClass. Two examples sell two units each but have different ordinary/super-voting classes. The TOE consumer re-exports toeSaleUnitsCannotIdentifySecurityClass. These are synthetic types, not an observed issuer register.

The standalone [dashiTRADE PR #3](https://github.com/chboishabba/dashiTRADE/pull/3) now requires issuer_id, instrument_id and share_class for the optional ShareClassSaleLink. SecuritiesSettlementLink rejects mismatched instrument ID; mixed ordinary/super share sales cannot be treated as a single-class instrument fill. No production Intent, BarExecution, broker or Nashi code was modified. **28/28 isolated Python tests passed**, with Git blob identities matching the exact GitHub source/test files. This is not Agda kernel verification or independent market evidence.

Original authorities: [ASIC Shareholder rights and responsibilities](https://www.asic.gov.au/for-business-and-companies/companies/company-share-and-shareholder-rules-and-changes/shareholder-rights-and-responsibilities) distinguishes share classes and company constitutional rules. [ASX/CHESS settlement](https://www.asx.com.au/markets/clearing-and-settlement-services/asx-settlement) addresses delivery-versus-payment of securities and cash, a separate source role. Neither a matched source label nor a DOI can certify actual legal beneficial ownership or company control. The original Ibrahim first-link navigation, Pareto/Zipf mathematical source authors, and separately prior-owned Monster 3B theorem claims remain independent.

**Genuine wall:** obtain same-person, same-instrument, same-issuer, same-class, time-matched actual ownership, tax, custody and payment data, plus independently observed physical service/capital outcomes. No additional synthetic evidence receipt can create those observations. ESD and newer divergent specialised TOE root modules remain untouched.

## 18. Net clearing and the exact source-identity repair (2026-10-28)

**New severe Max-Cut from the actual standalone code:** A structurally identical but independently created funding receipt was being accepted as the same transaction by a Python frozen dataclass fieldwise equality test. The bug was reproduced before fixing it. The new dashiTRADE source requires the exact local funding object identity, and separately matches issuer and instrument labels in the class link, submitted order and each synthetic fill. The fix rejects misleading duplicate-value joins. Python's local object identity remains **runtime-scoped**; it is not an externally authenticated same-owner or CHESS transaction event. Persistent data joins require legal identity and independent authoritative transaction receipts.

**New numerical Max-Cut:** Earlier Python Decimal addition could falsely mark an unbalanced route as balanced at 10^40 cash plus 1 borrowed unit because default 28-digit precision silently rounded. The repaired shadow uses exact scaled integer coefficients for levy, uncollected cash, funding balance, filled sale proceeds and logging, independent of ambient Decimal precision. All **34 exact-blob isolated Python tests pass** (source be5a60e437c8762ed03a0298ae08a109623dc647; tests f29d6780fed8323a519259551f995323588f01d4, both verified against actual GitHub blobs). Source-writing and executed Python tests remain separate from Agda kernel proof authority.

**Agda reuse and true type-level minimum cut:** Existing WealthTaxDashiTradeMarketMaterialBidiExact now has SettlementOwnershipWeld with explicit equalities for the original two-fill settlement's paid funding route, same aggregate units, and issuer/instrument source labels compared with the existing IdentifiedClassSettlement. No new generic source/identity logic: inherited INF proofs and the older Agda ContentAddressedTransitionIdentityExact owner retain mathematical and design priority.

**ASX batch settlement changes the observational unit.** The [ASX settlement services original primary source](https://www.asx.com.au/about/regulation/clearing-and-settlement-of-cash-equities-in-australia/settlement/settlement-services-and-pricing) describes Model 3 participant-level net batching, net securities obligations and net cash payments across positions. [ASX clearing](https://www.asx.com.au/about/regulation/clearing-and-settlement-of-cash-equities-in-australia/clearing) distinguishes executed trades, novation and resulting participant obligations. The new Agda ParticipantClearingBatch is deliberately a nonnegative net-receive fixture: one batch has zero cash buy/sell, another has gross buys = gross sells = 3, yet both report net received cash 0. The generic INF theorem then refutes *any* reconstruction of gross sales from that net cash projection alone. It does not infer every investor's line-item funding receipt from CHESS participant-level settlements.

**Original attribution and study-class controls:** ASIC shareholder-vote class rights, ASX CHESS settlement, Python's dataclass equality contract, Fagereng/Guiso/Ring Norwegian investor study and independent historic philosopher/social-scientist works are separate sources, not mutually validating real estate, corporate control or wealth-cap effect studies. Latest fleet PR #1409 proposes deterministic content-addressed IPFS refs for PNF logical shards; those hashes are process/transport provenance only, never semantic event equality or Monster representation. The previously owned Ibrahim 2017 first-link research and Ibrahim Monster 3B theorem work are separate. No ESD file, live trading authorization or specialist divergent TOE aggregate was edited.

**Status and wall:** New finite Agda terms are source-written and statically audited, NOT Agda-kernel-verified. Real-world promotion needs matched tax authority remittance receipts, brokerage fill/execution records, participant allocation to investor, original issuer share class and legal beneficial ownership, same-time financing and independently measured physical capacity/service outcomes. Sufficient data may not be publicly accessible. Further synthetic identity labels cannot replace them.

## 19. Verified exact-money implementation and net-clearing receipt (2026-10-28)

This round raised a live engineering issue beyond the earlier synthetic math: an actually unbalanced payment route was accepted at 10^40+1 due to Python's standard Decimal precision, and value-equality was mistaken for same transaction identity. Both were independently reproduced before repair.

The standalone [dashiTRADE draft PR #3](https://github.com/chboishabba/dashiTRADE/pull/3) has now changed (i) exact transaction-local identity plus separate issuer checks at order, fill and share-class linkage; (ii) context-independent, integer-scaled decimal sums for assessment, collected/unpaid cash, funding balance and settled proceeds. It retains the original logical-only shadow permission boundary and rejects pathological arithmetic spans. A separate 125-case Fraction rational oracle verifies high-magnitude/cents arithmetic even at Decimal precision 2. Exact committed source/test Git blobs match local executed copies; **36/36 isolated unittest tests passed**. No live trade or legal tax evidence.

The existing Agda wealth-tax/dashiTRADE Economics application reuses the earlier exact financing route, share-vote and two-fill settlement owner in SettlementOwnershipWeld with explicit proof obligations for same source-labelled funding, quantities, issuer and instrument. A new nonnegative participant-net clearing fixture shows equal zero net receipts can arise from no gross buys/sells or matched gross buys and sells of 3. The generic mathematical refutation of reconstructing gross sales from net cash is inherited from DASHI.Core.IntersectionalNonFactorability; not an independent theorem of the cited financial researchers. Exact branch readback: **19/19 source and import checks passed**, including 42 original topic rows. **Agda kernel has not typechecked this branch**; a static symbol match cannot establish correctness of the entire module.

ASX's primary clearing/settlement documentation identifies the distinct participant-level netting and irrevocable delivery-versus-payment mechanism (https://www.asx.com.au/about/regulation/clearing-and-settlement-of-cash-equities-in-australia/settlement/settlement-services-and-pricing). The earlier source root for issuer class rights is ASIC (https://www.asic.gov.au/for-business-and-companies/companies/company-share-and-shareholder-rules-and-changes/shareholder-rights-and-responsibilities). Python dataclass fieldwise equality belongs to the Python runtime standard (https://docs.python.org/3.13/library/dataclasses.html). Do not treat transport digests or source-content equality as proven same actor/event identity; later Agda fleet/IPFS PR #1409 owns its independent deterministic transport provenance and does not supply finance evidence or Monster proof authority.

For actual policy-market and material-causal claims, the wall remains same-person legally filed taxation, taxpayer payment-source/borrowing/custody records, linked issuer voting rights, participant-to-investor net clearing allocations and physical investment/care capacity. None is constructed from a synthetic receipt or the mere names of original empirical sources.

## 20. General tax, settlement, Pareto and material lemmas (28 October 2026)

### Max-cut result

This continuation changes the mathematical level. The earlier illustrative numerical cases remain named finite witnesses. The new terms discharge the first generic tranche of the explicit 77-obligation roadmap without cloning mathematical owners:

- **Tax / stdlib reuse:** Base source now imports existing Agda standard-library Nat order/truncation theorems. For all natural-number wealth and threshold inputs, it proves the *hypothetical assessment-day* complete-payment remainder equals min(wealth, threshold), zero excess below threshold, tax monotonicity at fixed threshold, and upper bound by assessed stock. The original law is not enacted; real collection is independent.
- **Arbitrary finite fills:** Trade application models reconciled submitted/executed/settled counts and folds any finite List of settled price–quantity receipts. Under explicit reconciliation, settled count is bounded by executed count and by order size. A declaration of a filled order does not create its evidence.
- **Pure share transfers:** A two-account seller/buyer pure transfer preserves total already-issued units. Issuance, cancellations, collateral rights and true beneficial owner identification are separate.
- **Real capital and care:** A physical stock-flow receipt carries independently supplied installed-before/commissioned/retired/installed-after values; its stock balance entails the conditional retirement-adjusted capacity identity. Care receipts explicitly bound delivered hours by supplied staff and equipment capacities. Budget spending does not construct either receipt.
- **Pareto:** Reused canonical DASHI.Core.AdmissibleConsumerMDLHyperfabricExact CostHyperfabric/WeaklyDominates; added reflexivity and transitivity proofs. A synthetic two-axis admin-cost versus care-shortfall comparison is incomparable, showing the order need not be total. This **does not** prove a unique or non-unique optimal tax rate in society, so that larger I08 obligation stays OPEN.
- **Participant allocation:** Given independently reconciled finite investor gross-buy/gross-sell cash allocations, their sums agree with an inherited nonnegative net-receiving participant balance. Without allocation evidence a net participant receipt still does not identify any taxpayer.

### Prior roots, formal owners and verification boundaries

Mathematical prior art here is the Agda standard-library natural-number arithmetic and the existing DASHI CostHyperfabric, INF/nonfactorability, trading, source-attribution and economic-work proof owners. Original economists, historical political theorists, legal sources, and the independent Ibrahim Monster 3B line retain their authorship; none originated these newly source-written Agda application terms. In particular, Pareto's work on income distributions is an original historical root distinct from the specific modern Pareto-order/CostHyperfabric code.

Current original empirical external context: [Fagereng, Guiso and Ring, NBER Working Paper 35262 (May 2026)](https://www.nber.org/papers/w35262) reports strong but slow Norwegian equity-portfolio adjustments to wealth-tax-induced incentives, not an observed hard annual wealth cap. [ASX Settlement Procedure Guidelines, §7.4 (official ASX)](https://www.asxonline.com/content/dam/asxonline/public/documents/manuals/chess-asx-settlement-procedure-guidelines/asx015347.pdf) spells out instrument/HIN-sensitive netting, including exceptions. Neither source is a proof of these conditional Agda equations or a live dashiTRADE execution.

Status: the newly source-written conditional theorem obligations are catalogued by ID in [WealthTaxCompletionLemmaLedger20261028.md](WealthTaxCompletionLemmaLedger20261028.md), now **39 D / 9 R / 29 N**. Static symbol/source/TOE checks passed, but this branch does not have an observed Agda kernel result. The existing standalone dashiTRADE 36/36 Python regressions were re-executed locally and the original standalone trading execution remains unchanged. No ESD surfaces, specialist diverged master TOE roots or prior Monster 3B proof owners changed.
