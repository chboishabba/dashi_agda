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

