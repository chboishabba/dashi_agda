# Wealth-tax × dashiTRADE: exact completion roadmap and scoped lemma ledger

Created 2026-10-28. **77 named formal obligations** across nine groups: 60 source-written (D), 11 owned by existing reusable sources (R), 6 remaining external identity/evidence contracts (N). D and R are NOT equivalent to an observed Agda kernel pass. N are *proposed names*, not already implemented.

Source PRs: [dashi_agda #1277](https://github.com/chboishabba/dashi_agda/pull/1277); [dashiTRADE #3](https://github.com/chboishabba/dashiTRADE/pull/3). This ledger defines the complete finite scope **for this economics/trade research release**; it is not a finite list of all possible theorems in macroeconomics or physics. Reuse first; do not edit ESD or overwrite diverged TOE root files.

## Formal lemma and record obligations

### A. Tax base and assessment-day ceiling (8)

- **A01 [D]** `incomeTaxIsNotStockCap` — Stock and annual income taxes are distinct constructors.
- **A02 [D]** `vacancyTaxIsNotWealthCap and inheritanceTaxIsNotAnnualWealthLevy` — Different legal tax bases remain typed.
- **A03 [D]** `sourceAIProposedRatesAreNotVictoriaLaw` — AI-suggested 1/2/5% idle equity is not the enacted Victoria VRLT schedule.
- **A04 [D]** `annualSnapshotIsNotContinuousBound` — Assessment-time cap does not bound all between-assessment states.
- **A05 [N]** `netWealthBalanceIsWellTyped` — One timestamp and unit, with debt and beneficial-ownership exclusions.
- **A06 [D]** `netWealthAfterFullyPaidExcessEqualsMin` — Given full collection, after-payment wealth equals min(W,K).
- **A07 [D]** `hundredPercentLiabilityZeroBelowThreshold` — Generic threshold/truncated subtraction cases.
- **A08 [D]** `wealthLiabilityMonotoneAtFixedThreshold` and `wealthLiabilityNeverExceedsAssessedWealth` — General fixed-threshold monotonicity and upper bound.

### B. Fiscal collection, budget and care (8)

- **B01 [D]** `liabilityAloneDoesNotDetermineCollection` — Same assessed liability permits differing collected cash.
- **B02 [D]** `collectionCostsNotDeterminedByCash` — Collected cash does not determine administration cost.
- **B03 [D]** `cashReceiptsDoNotDetermineCareAppropriation` — Collected receipts do not choose spending.
- **B04 [D]** `taxDueNotAdequateToInferActualCollection` — Query adequacy defect and negative witness.
- **B05 [D]** `riskSignalAloneIsNotTaxAuthority` — AI risk feature does not define an effective statutory base.
- **B06 [D]** `remittanceBoundedByAssessedLiabilityUnderNoPenalties` — State conditions excluding penalties, refunds and interest.
- **B07 [D]** `cashBudgetConservationWithCostsAndTransfers` — Cash receipts, carry, debt and actual spending form balanced budget.
- **B08 [D]** `careAppropriatedDoesNotDetermineCareDelivered` — Appropriation cannot create service hours without resources.

### C. Payment funding and market sale paths (9)

- **C01 [D]** `FundingRoute.fundingBalances` — Cash + new debt + gross sales equals tax cash + execution costs.
- **C02 [D]** `noOtherFundingImpliesSaleProceeds` — With zero cash/debt, sale cash equals tax plus execution costs.
- **C03 [D]** `paidTaxCannotDetermineUnitsSold` — Equal tax paid, different sale quantities.
- **C04 [D]** `saleVolumeCannotDetermineExecutionCost` — Equal quantities, different costs.
- **C05 [D]** `saleVolumeCannotDeterminePhysicalCapacity` — Share volume does not identify machines.
- **C06 [N]** `cashSourceUseIsSingleCounted` — Avoid counting same currency claim as cash, debt and sale.
- **C07 [D]** `loanProceedsIncreaseLiabilities` — Borrowed proceeds create offsetting debt.
- **C08 [D]** `disposalPreservesExternalAssetTransferAccounting` — Seller/right transfer to buyer and fees cannot erase plant.
- **C09 [N]** `routeFundingFeasibleGivenLiquidityCollateralAndTiming` — Balanced ledger does not guarantee funding availability.

### D. Trade, fills and settlement (12)

- **D01 [R]** `Dream.buyViabilityDoesNotFactorThroughDirection` — Trade signal does not supply BUY permission.
- **D02 [R]** `Dream.holdAlwaysAvailable` — HOLD is admissible in inherited finite model.
- **D03 [R]** `TradingJointPreconditionFabricExact.expansiveNotJointlyAdmissible` — Marginal permission does not imply joint permission.
- **D04 [R]** `ContentAddressedTransitionIdentityExact.SameTransitionSpine` — Exact transition identity across stages is more than a hash.
- **D05 [D]** `submittedOrderDoesNotDetermineSettlement` — Submitted order does not specify settled shares.
- **D06 [D]** `executionDoesNotDetermineSettlement` — Executed amount does not specify settled shares.
- **D07 [D]** `twoFillCashConservation` — Two filled unit prices 1 and 2 produce gross settled cash 3.
- **D08 [D]** `priorCashReceiptHasNoForwardSettlementLink` — Future settlement does not directly finance earlier remittance.
- **D09 [D]** `genericExecutedCountBoundedBySubmitted` — Finite list of fills cannot exceed authorized order under contract.
- **D10 [D]** `genericSettledCountBoundedByExecuted` — All partial fills and unsettled remainders balance.
- **D11 [D]** `genericSettledProceedsIsExactPriceQuantitySum` — Arbitrary number of exact fills, no ambient decimal rounding.
- **D12 [D]** `uniqueFillIdentityAndMonotoneEventTime` — Unique IDs, instrument and 4-stage timestamp agreement.

### E. Share class and control identity (9)

- **E01 [D]** `ownerWeightedVotes and afterTransferVotesRemainAboveHalf` — Finite super-vote example.
- **E02 [D]** `quantityCannotFixVotingControl` — Same sale count can leave 34/50 versus 16/50 voting power.
- **E03 [D]** `FundingVoteReconciliation` — Per-class sold units and before/after owned units balance.
- **E04 [D]** `saleVolumeCannotIdentifyInstrumentClass` — Quantity does not determine ordinary versus super-voting security.
- **E05 [D]** `SettlementOwnershipWeld` — Exact synthetic funding/quantity/issuer/instrument label agreement.
- **E06 [D]** `shareClassTransferPreservesIssuedSupply` — Seller/buyer/treasury/issuance/cancellation legal share changes.
- **E07 [N]** `authenticatedOwnerIssuerInstrumentClassKey` — Evidence-checked beneficial owner, issuer, security and class.
- **E08 [D]** `controllingVotesRequireVerifiedRightsAndAgreements` — Majority arithmetic does not determine effective legal control.
- **E09 [D]** `persistentTransactionIdentityCannotFollowFromValueOrDigest` — Local object identity, value equality, content hash and registry identity differ.

### F. Clearing and investor attribution (7)

- **F01 [D]** `ParticipantClearingBatch.netAccounting` — Finite gross sell/buy to net-receipt accounting.
- **F02 [D]** `netReceiptCannotRecoverGrossTurnover` — Net zero can hide offsetting gross activity.
- **F03 [D]** `investorAllocationsSumToParticipantObligation` — Broker/custodian allocations aggregate to participant totals.
- **F04 [D]** `deliveryVersusPaymentCashAndTitleCoMove` — Conditional securities/cash finality with correct settlement authority.
- **F05 [D]** `aggregateNetPositionsRespectGrossCashAndSecurityTotals` — Signed buy/sell/receive/pay variants with no silent cancellation.
- **F06 [D]** `participantNetStatementDoesNotIdentifyIndividualTaxpayer` — A net participant receipt is not an individual's payment trace.
- **F07 [N]** `actualSettlementFinalityRequiresOfficialReceipt` — Simulated close event cannot create authentic custody receipt.

### G. Physical capacity and care (7)

- **G01 [D]** `saleVolumeCannotDeterminePhysicalCapacity` — Existing finite distinct installed-machine example.
- **G02 [D]** `careCannotFactorThroughTaxReceipt` — Same tax cash does not fix care outcome.
- **G03 [R]** `AIEconomicUsefulWorkTimeSeriesExact and UnitEconomicsMarginExact` — Useful work and positive return do not follow from volume.
- **G04 [D]** `physicalCapitalStockFlowConservation` — Existing stock + commissioned - retired = next stock with time.
- **G05 [D]** `deliveredCareHoursBoundedByStaffAndEquipment` — Staff time, buildings and equipment constrain care capacity.
- **G06 [D]** `energyMaterialsAndConstructionFeasibility` — Installed productive output consumes time and physical inputs.
- **G07 [D]** `financialClaimChangeDoesNotIdentifyPhysicalOutput` — Generic conditional non-factorability rather than physical law.

### H. Attribution, evidence and theorem authority (8)

- **H01 [R]** `AttributedSourceCore.citationImportsProofIsFalse` — External citation does not discharge kernel theorem.
- **H02 [R]** `SourceAttributionPromotionBoundaryExact.sameContentDoesNotAutoPromoteToIndependentProducer` — Reprints and summaries do not create independent sources.
- **H03 [R]** `EvidenceHyperfabricExact and SnowballAttributionProvenanceInvariantExact` — Preserve independent evidence fibres and genealogy.
- **H04 [R]** `ContentAddressedTransitionIdentityExact.canonicalTransitionIdentityBoundary` — Digest is not event identity/collision-freedom.
- **H05 [D]** `toePaperCannotSupplyKernelCertification` — Agda source and publication are not compiler receipts.
- **H06 [R]** `authorAndProofOwnershipAreDisjointReceiptTypes` — Original study, repository theorem, code, executed tests, Agda kernel all typed differently.
- **H07 [R]** `originalSourceProducerIsNotDerivedSummary` — Primary and derivative reports never become two independent observations.
- **H08 [N]** `measuredPolicyEffectRequiresSameObjectInputs` — Conditional matched person/security/tax/payment/time/outcome promotion.

### I. Pareto comparison and causal humility (9)

- **I01 [D]** `rivalPolicyTaxBasesRemainComparableButDistinct` — Compare wealth/income/inheritance/gains/land/vacancy on typed metrics.
- **I02 [D]** `policyScenarioRequiresStatuteOrHypotheticalTag` — Hypothetical hard cap not mislabeled enacted.
- **I03 [D]** `finitePolicyStateTransitionPreservesAccounting` — Across-period wealth/debt/security/care stocks balance.
- **I04 [D]** `behaviouralResponseParametersAreExplicitAssumptions` — Migration, credit and investor behaviour are not given theorems.
- **I05 [D]** `sameInitialStateDifferentInterventionComparison` — Explicit baseline and treatment labels.
- **I06 [D]** `paretoDominancePreorder` — Reflexive and transitive objective-vector comparison.
- **I07 [D]** `finiteParetoFrontierIsNonempty` — Nonempty finite feasible choice set has non-dominated element.
- **I08 [D]** `noUniqueOptimalTaxRateFromParetoOrderAlone` — Partial ordering does not select welfare weights.
- **I09 [D]** `syntheticModelCannotIdentifyObservedCausalEffect` — Separate case-study, controls and causal identification receipts.

## External independent evidence obligations (not Agda lemmas)

- **X01** Primary enacted tax statute, jurisdiction, base and assessment period.
- **X02** Assessed wealth, debt, exclusions and ownership with original timestamp.
- **X03** Legally issued liability, collection, adjustments, refunds and costs.
- **X04** Payment-source cash, loan, collateral, sales or separate bridge finance.
- **X05** Real order/fill IDs, price, fee and seller holdings.
- **X06** CHESS/broker/issuer custody settlement and participant-to-investor allocation.
- **X07** Authentic company share-class voting rights and effective control agreements.
- **X08** Measured capital spending, assets commissioned, energy, staffing and delivered care.
- **X09** Matched controls, pretrends, migration and confounder sensitivity.
- **X10** Independent/out-of-sample replication, uncertainty and null-result disclosure.

## Release gates (engineering, not theorems)

- **K01** Lock original owner and exact SHA/Agda/stdlib/Python dependency receipt.
- **K02** Discharge N terms or label residuals OPEN; no fake complete status.
- **K03** Observed Agda kernel pass of 4 economics owners and TOE consumer, zero unsafe proof escapes.
- **K04** Exact Python/Agda fixture equivalence, adversarial test and no live order execution.
- **K05** Rebase/merge 152 newer master-only commits without resetting three evolving TOE root files; register Economics/TOE imports; fix master economics escaped newline.
- **K06** Review and merge both PRs and publish source-written/tested/kernel/empirical tiers separately.

## Minimal sequencing / completion decision

F0 = capture source owner, master comparison and exact heads. F1 = kernel typecheck plus syntax fix. F2 = generic accounting, settlement and identity completion (A–F). F3 = source-owned material constraints (G) and attribution firewalls (H). F4 = conditional rival policy Pareto frontier (I) with no measured-effect assertion. F5 = cross-repo shadow conformance and master TOE merge. F6 = real-world X01–X10 study, or publish them as OPEN if inaccessible. Formal release may finish at F5; an empirical finding cannot.

**Attribution:** All dated mathematical, political and economic original authors keep original ownership; reuse DASHI theorem owners as owners, not copied proofs. The independent Ibrahim 2017 Wikipedia FLN and existing Ibrahim Monster 3B work remain separate. No numerical/character/IPFS coincidence creates same-object identity or a causal claim. Synthetic filled receipts are not exchange records, shareholder registers, legal assessments, market execution, care hours or laws of physics.

## 2026-10-28 proof expansion: nine obligations now source-written

The next pass constructs nine conditional general results by reusing the Agda standard library and existing DASHI theorem owners. Ledger now has 37 D, 9 R, 31 N. Source writing is NOT an observed Agda kernel check.

- A06-A08: for all natural-number thresholds, under full assessment-day collection the modeled remaining stock equals the minimum of stock and threshold. Truncated liability vanishes below the threshold, is monotone at fixed threshold, and never exceeds assessed wealth.
- D09-D11: generic balanced order records yield executed <= submitted, settled <= executed, and settled <= submitted. An arbitrary finite price/quantity list has an exact fold for gross proceeds; declared cash must carry a separate explicit equality proof. This does not assert any real exchange fill.
- E06: an already-issued share-class transfer conserves seller/buyer combined unit count, given exact before/after seller and buyer reconciliations.
- G04-G05: physical plant has its own before, commissioning, retirement and after-stock accounting. Actual care service hours are separately bounded by supplied staff and equipment capacities.

All these records are model-conditional. No actual tax, legal control, worker, energy or machine state is inferred. No new unsafe Agda options or protected ESD edits. The standalone shadow Python suite was independently re-executed with 36 passing tests and remains unchanged.


## Pareto source-owner continuation, 2026-10-28

The existing DASHI.Core.AdmissibleConsumerMDLHyperfabricExact owns the multi-axis WeaklyDominates definition. The economics adapter now imports it and supplies paretoDominanceReflexive and paretoDominanceTransitive. A two-option synthetic cost-vector example proves that two distinct feasible-looking options can be incomparable when lower administration costs compete against increased care capacity. This is source-written, not an observed Agda kernel result.

I06 and a finite incomparability witness relevant to I08 are source-written, but I08 stays OPEN; I08 must not be misconstrued as a proof of the real-world unique optimum of any enacted tax. I07 (existence of an undominated point in nonempty finite feasible set) remains open. No source, proof-author or Ibrahim 3B ownership was reassigned.

**Ledger: 42 D, 9 R, 26 N.**


## Participant-to-investor reconciliation (F03), 2026-10-28

F03 is now source-written: `ParticipantInvestorAllocation` stores arbitrary finite lists of investor sale/purchase cash amounts and proofs that the sums equal a participant-level gross sell/gross buy batch. `investorAllocationsSumToParticipantObligation` composes these source-supplied equations with the previous participant-net balance using transitivity and congruence. The TOE consumer imports the same proof. This is a **conditional arithmetic conservation theorem**; it does not recover a named investor, tax payer, security ID or real ASX/CHESS source event from the participant's net receipt. F06/F07 (specific investor identity and official settlement finality) remain OPEN. No duplicate new general clearing library was created.

**Ledger tally: 42 D, 9 R, 26 N.**

## Directional clearing and conditional single-instrument DvP

The earlier receiver-only net-cash batch is extended by a payable/receivable direction tag. The conditional SingleInstrumentDvPBatch records separate gross/net cash and security quantities, matched direction, and simultaneous finality at an externally supplied epoch. F04/F05 now have source-written dependent contracts but do not establish real CHESS finality or identify a real taxpayer. F07 remains OPEN. No live trading code changes.

**Current ledger: 42 D, 9 R, 26 N.**


## Matched lending balance (C07), 2026-10-28

A new conditional MatchedBorrowingBalance requires both cash and liability to increase by the *same* borrowed units. It reuses the Agda standard library natural-number subtraction cancellation law to prove that cash minus debt, truncated at zero, is unchanged by that perfectly matched borrowing event. This is a genuine conditional algebraic result about the selected two-line financial ledger, not proof of loan accessibility or valuation, interest, collateral, lender risk, later repayments or tax-law effects. Both the original application and TOE consumer retain the no-automatic-credit authority boundary.

**Ledger: 42 D, 9 R, 26 N.**

## 2026-10-28 continuation: four substantive interfaces advanced

Existing application owner: DASHI/Economics/WealthTaxDashiTradeMarketMaterialBidiExact.agda.
Existing TOE consumer: DASHI/Unified/WealthTaxEvidenceNonPromotionTOEExact.agda.

**Four N → D source-written obligations (46 D / 9 R / 22 N):**

- **B06:** NoAdjustmentCollection reconciles principal remitted, outstanding principal and the assessed liability. remittanceBoundedByAssessedLiabilityUnderNoPenalties derives the remittance bound from that identity. No penalty, refund, interest, tax statute or genuine assessment is inferred.
- **B07:** ReconciledPublicCashBudget separates administrative outflow, transfer outflow, care appropriation and cash retained. cashBudgetConservationWithCostsAndTransfers proves modeled outflow is no greater than available cash, conditional on an exact balanced receipt.
- **B08:** careAppropriatedDoesNotDetermineCareDelivered supplies two same-appropriation/different-delivered-hours counterworlds. It reuses the original IntersectionalNonFactorability theorem owner. This does not measure a clinical service.
- **F06:** participantNetStatementDoesNotIdentifyIndividualTaxpayer supplies two distinct synthetic investor keys sharing the same participant clearing batch. It proves net statement alone cannot determine investor identity. Keys are illustrative, NOT authenticated taxpayer/holder identities.

**Partial advances which remain N:**

- **C09:** routeBalanceDoesNotEstablishLiquidityOrTiming prevents upgrading balanced payment totals into accessible financing. Real credit/collateral/liquidity and settlement timing still require evidence.
- **G06:** FixedInputConstructionFeasibility adds conditional per-unit energy and material budget constraints. It does not calibrate inputs, commission actual plant or certify resource availability.
- **I08:** finiteParetoTradeoffHasTwoDistinctMinimalOptions and paretoMinimalityCannotUniquelySelectCheapAdministration identify two undominated, distinct outcomes in the existing two-option illustrative cost hyperfabric. This is a finite countermodel, not general finite frontier enumeration (I07) or an optimal tax-rate result.

**Independent roots:** ASX official CHESS Model 3/DvP and netting description; Fagereng–Guiso–Ring 2026 NBER WP35262. They bound institutional/empirical interpretation; they do not own the synthetic finite proof. The existing DASHI proof owners retain theorem ownership. Existing Ibrahim original FLN producer and earlier Monster 3B lineages are unrelated. Content identity, proof-source ownership, executed checks and authenticated transactions remain distinct.

**Verification ceiling:** new Agda terms have been committed and structurally read back; NO observed Agda kernel typecheck or exact-head GitHub Actions receipt. The existing dashiTRADE shadow adapter is unchanged. No protected ESD surfaces or specialist TOE roots are edited. All 42 original topic inventory rows remain in scope; coverage is not a causal or formal certificate.

**Actual walls remain:** D12 generic fill IDs/chronology; A05 asset/debt/beneficial-owner valuation; E07–E09 authenticated owner/rights/transaction identity; F07 custody finality; H06–H08 evidence authority; I01–I07/I09 causal multi-policy framework; full compiler pass, mainline integration, X01–X10 external evidence and cross-runtime conformance.

## 2026-10-28 finite fill chronology continuation (D12)

- **D12 N → D:** TimestampedFill includes issuer/class labels and an explicit four-stage per-fill chronology: submission ≤ execution ≤ clearing ≤ settlement. TokenAbsent and UniqueFillTokens define a recursive duplicate-token exclusion for arbitrary finite lists, with AllFillLabelsMatch requiring issuer/class agreement throughout a batch.
- ChronologicalIdentifiedFillBatch exposes the proofs and uniqueFillIdentityAndMonotoneEventTime projects them. TwoIdentifiedChronologicalFills supplies a positive finite witness; duplicateSevenTokenRejected supplies the same-token negative witness.
- The theorem is **source-written, not kernel-certified**. A token is unique only within the supplied list; a repeated token in another batch, a forged label, an exchange clock offset, a settlement rejection, and a real custody identity still require separate authority. D12 contains no cross-fill sorting requirement and must not be represented as one.
- No new clearing adapter or live broker execution. The original dashiTRADE PR #3 Python shadow suite remains a separate executable implementation, not proof of this Agda type.

**Current scoped ledger status: 47 D / 9 R / 21 N, out of 77.** No observed Agda compiler certificate, and no X01–X10 same-object empirical record suite.

## 2026-10-28 D11 × D12 ordered identity/cash join

The earlier separate finite fill uniqueness and cash conservation receipts did not establish that their *lists* were related. JoinedPriceIdentityBatch now carries one ordered list of (timestamped ID, priced fill) pairs. It requires exact equality between that full price/quantity projection and the settled cash batch's original list, unique local tokens, and common issuer/class labels. joinedIdentityAndCashReconcile composes the prior D11 cash equation with the D12 token property. A two-fill positive witness has gross cash 3. This does not verify real exchange identity, custody finality or tax payment. All construction is source-written; compiler certification remains unobserved. No status tally is changed: **47 D / 9 R / 21 N**.
## 2026-10-28 reused original-owner attribution boundaries (H06–H07)

The existing DASHI.Economics.SourceAttributionPromotionBoundaryExact owner already distinguishes original source propositions, formal construction, theorems and promotion steps. It independently proves sourceArgumentDoesNotAutoPromoteToDASHIFormalisationOwnership and secondaryReportDoesNotAutoPromoteToPrimaryAuthority. The TOE consumer now re-exports these exact existing proofs. Thus H06 and H07 are **R (reused prior owners)**, NOT independently authored new proofs, and not kernel-certified at this branch head. This closes the duplicated-work gap without copying a proof or giving original authors new repo theorem ownership. Different receipt authority levels still require an actual source producer for a valid empirical promotion.

**Current scoped ledger status: 47 D / 11 R / 19 N, out of 77.** The previous 47/9/21 tally remains an historical snapshot. No signature, matching digest, content replica, Wikipedia hyperlink, Ibrahim Monster 3B result or LLM summary identifies a real taxpayer or proves a policy outcome.

## 2026-10-28 source-owned stock, identity and rival-policy continuation

**Current exact ledger: 59 D / 11 R / 7 N = 77.** Twelve obligations moved from N to D as model-conditional Agda source constructions, NOT observed Agda kernel results or empirical accomplishments. The historical previous tallies remain in earlier sections as versioned snapshots.

**D source-written (theoretical scoped completion; actual-world validation remains X01–X10):**

- C08: disposalPreservesExternalAssetTransferAccounting reuses the existing E06 share seller/buyer conservation and requires separately witnessed plant invariance.
- E08: controllingVotesRequireVerifiedRightsAndAgreements gives two equal-vote/different-assumed-control counterworlds, blocking vote-count-only claims of effective legal control.
- E09: persistentTransactionIdentityCannotFollowFromValueOrDigest blocks factorisation from an equal synthetic digest label into different synthetic event labels. No cryptographic collision is asserted.
- G06: FixedInputConstructionFeasibility carries independently specified energy and material requirements. energyMaterialsAndConstructionRequireSeparateInputs projects the two necessary input constraints.
- G07: financialClaimChangeDoesNotIdentifyPhysicalOutput uses the established nonfactorability owner for same-claim/different-output worlds.
- I01: RivalTaxBaseComparison reuses original Tax.Policy, Tax.TaxBase and taxBase, preserving separate legal objects while allowing declared common cost units.
- I02: TaggedPolicyScenario and StatutoryPolicyAdmission keep hypotheses separate from externally validated enactment evidence; no such legal evidence is synthesized.
- I03: FinitePolicyAccountingPeriod requires before/after stock and flow reconciliation.
- I04: ExplicitBehaviourAssumptions keeps migration, credit and slow portfolio-adjustment assumptions in separate named coordinates; it is not an estimated response.
- I05: SharedInitialPolicyComparison requires equality of baseline/intervention opening stock; this is not sufficient for causal identification.
- I08: noUniqueOptimalTaxRateFromParetoOrderAlone exhibits two distinct illustrative rate tags behind already-demonstrated incomparable Pareto-minimal outcomes. It refutes universal unique-choice inference, not a specific enacted tax rate.
- I09: syntheticModelCannotIdentifyObservedCausalEffect supplies same-forecast/different-external-coordinate worlds; the external coordinate is **synthetic fixture input**, not real observations.

**Partial source-written work, intentionally retained N because the stronger evidence/identity target is unpaid:**

- A05: ScopedNetWealthSnapshot reconciles gross/included/excluded assets and debt, but same-object valuation, beneficial-owner exclusion, currency validity and time authority remain unverified.
- C06: TaggedFundingReceipt proves each tag contributes to exactly one channel. This does not prevent two forged tokens referring to one real cash source across receipts.
- C09: FinancedRouteAdmission requires liquidity limit, collateral/credit limit and settlement-before-tax evidence. Constructing these *assumed* proofs does not demonstrate actual financing access.
- E07: OwnerIssuerSecurityAdmission requires independent registry validity and owner/issuer/class name matches. It does not verify cryptographic signatures or true beneficial ownership.
- F07: OfficialSettlementAdmission requires an independent official receipt validation predicate. There is no actual ASX/CHESS/custodian receipt or checker invocation.
- H08: MatchedPolicyEffectAdmission requires independent tax/custody/outcome/causal-design checks plus same-person and same-security key equalities. No real matched panel or identified causal effect is presented.
- I07: a two-option finite Pareto witness is available; general nonempty finite feasible-frontier existence using the original canonical multi-axis order remains open.

**Additional complete source-level guards:** the original TOE consumer re-exports the new application results. The source/topic checker now requires the corresponding symbols, 42 topic rows and canonical imports. Existing economics and provenance theorem owners are not copied. No modified protected ESD surface, no specialist TOE facade overwrite, no live dashiTRADE executor change.

**Original source ownership and interpretation boundaries:** ASX owns CHESS Model 3 DvP / participant netting descriptions; Andreas Fagereng, Luigi Guiso and Marius A. K. Ring own NBER 35262 (May 2026) Norwegian portfolio evidence. Neither validates the hypothetical 100%-above-threshold annual cap. The original 2017 Ibrahim Wikipedia first-link lineage and independently owned Ibrahim Monster 3B results are not tax-system proof producers. A later reprint, code hash or matching character fingerprint does not establish independence or same-object identity.

**Verification ceiling:** commits establish repository source writing only. No Agda compiler is installed in this execution environment; exact-head Agda kernel checking is NOT observed. Static guards and bounded Python arithmetic checks are not interchangeable with typechecking. No production or real-world observations follow.

## 2026-10-28 I07 constructive ranked finite-frontier partial proof

The original multi-axis Pareto hyperfabric owner is unchanged. The existing economics application now includes a generic structurally recursive finite arg-minimum construction:

- RankedMember: source-local proof of membership in a finite list.
- FiniteRankMinimum and finiteNonemptyRankMinimum: for any Nat ranking of any nonempty finite population, return a member with no larger rank than any other listed member, using standard-library ≤-total, ≤-trans, ≤-refl.
- rankOrderCannotCycle: rejects a ≤ cycle with one strict successor step.
- StrictlyDominatesAdmissible: interprets strict improvement using the original Pareto.WeaklyDominates on Pareto.AdmissibleStratumPoint, which already carries feasibility and consumer adequacy.
- finiteParetoFrontierNonemptyGivenStrictRank: takes a supplied rank-decrease hypothesis for every strict Pareto improvement and constructs a listed admissible member that cannot be strictly dominated by another listed admissible member.

**Proof scope:** This is an arbitrary-list constructive theorem with an EXTRA assumption: a Nat ranking strictly decreasing on strict Pareto improvements. It does **not** prove that such a rank exists for an arbitrary finite multi-axis cost fabric, that the list enumerates every feasible alternative, or that the rank faithfully reflects measured costs. I07 therefore **remains N** for the unrestricted nonempty finite feasible-frontier theorem. This partial source construction does not change 59 D / 11 R / 7 N. No Agda kernel typecheck was observed, and none of the model examples selects a real tax rate.

## 2026-10-28 completed scoped finite-axis Pareto source term (I07)

The previous rank-assumption-only construction is now complemented by a derived finite-axis theorem.

- finiteAxisCostSum sums the original, named Pareto.CostHyperfabric axis costs over an explicitly enumerated finite list.
- finiteAxesReverseOrStrict uses the standard-library decidable Nat order. For a weak-dominance pair, it produces either reverse inequalities on ALL listed axes or a witness of strict improvement at an exact axis.
- strictImprovedAxisFromFiniteCoverage uses a supplied *complete finite-axis enumeration* to rule out the reverse case whenever strict dominance is given.
- finiteAxisSumStrict proves strict summed-rank reduction from coordinatewise weak dominance and that strict-coordinate witness.
- finiteParetoFrontierIsNonempty reuses the earlier constructive finiteNonemptyRankMinimum and finiteParetoFrontierNonemptyGivenStrictRank owners. Unlike the earlier version, the new public theorem DERIVES the rank-decrease proof from complete finite-axis cost data. It returns a member of any nonempty finite list of already-admissible, consumer-adequate candidates that no other listed candidate strictly Pareto-dominates.

**I07 changes N → D within this release's declared scope:** the finite population is nonempty, every population member is admitted, and the axis language has a caller-supplied complete *finite* enumeration. This does not prove the same result with infinitely many unenumerated axes, does not verify that every economically feasible policy is enumerated and does not rank incomparable alternatives into a uniquely preferred policy. The source-written theorem is NOT an Agda compiler receipt. Its own full-axis and missing-axis bounded Python falsification check is executed separately.

**Original mathematical roots:** the finite-order minimal-element result long predates this repository. Emmerich and Deutz (2018), "A tutorial on multiobjective optimization: fundamentals and evolutionary methods", Proposition 6, DOI 10.1007/s11047-018-9685-y, is an explicit published exposition, not claimed original invention of the theorem. The novel repository terms are ChatGPT-assisted source writing under Johl Brown's research direction; existing DASHI Pareto theorem owners remain the original code owner. Earlier Ibrahim first-link and Monster 3B claims are separate, and no new Monster correspondence is asserted.

**Current ledger tally: 60 D / 11 R / 6 N = 77.** Residual A05/C06/C09/E07/F07/H08 still require authenticated source/financial/regulatory/causal same-object evidence rather than a new free-floating synthetic theorem. Kernel typecheck and current-master convergence are separate release gates.

