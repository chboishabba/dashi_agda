# Wealth-tax × dashiTRADE: exact completion roadmap and scoped lemma ledger

Created 2026-10-28. **77 named formal obligations** across nine groups: 42 already source-written (D), 9 owned by existing reusable sources (R), 26 new required proofs/contracts (N). D and R are NOT equivalent to an observed Agda kernel pass. N are *proposed names*, not already implemented.

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
- **B06 [N]** `remittanceBoundedByAssessedLiabilityUnderNoPenalties` — State conditions excluding penalties, refunds and interest.
- **B07 [N]** `cashBudgetConservationWithCostsAndTransfers` — Cash receipts, carry, debt and actual spending form balanced budget.
- **B08 [N]** `careAppropriatedDoesNotDetermineCareDelivered` — Appropriation cannot create service hours without resources.

### C. Payment funding and market sale paths (9)

- **C01 [D]** `FundingRoute.fundingBalances` — Cash + new debt + gross sales equals tax cash + execution costs.
- **C02 [D]** `noOtherFundingImpliesSaleProceeds` — With zero cash/debt, sale cash equals tax plus execution costs.
- **C03 [D]** `paidTaxCannotDetermineUnitsSold` — Equal tax paid, different sale quantities.
- **C04 [D]** `saleVolumeCannotDetermineExecutionCost` — Equal quantities, different costs.
- **C05 [D]** `saleVolumeCannotDeterminePhysicalCapacity` — Share volume does not identify machines.
- **C06 [N]** `cashSourceUseIsSingleCounted` — Avoid counting same currency claim as cash, debt and sale.
- **C07 [D]** `loanProceedsIncreaseLiabilities` — Borrowed proceeds create offsetting debt.
- **C08 [N]** `disposalPreservesExternalAssetTransferAccounting` — Seller/right transfer to buyer and fees cannot erase plant.
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
- **D12 [N]** `uniqueFillIdentityAndMonotoneEventTime` — Unique IDs, instrument and 4-stage timestamp agreement.

### E. Share class and control identity (9)

- **E01 [D]** `ownerWeightedVotes and afterTransferVotesRemainAboveHalf` — Finite super-vote example.
- **E02 [D]** `quantityCannotFixVotingControl` — Same sale count can leave 34/50 versus 16/50 voting power.
- **E03 [D]** `FundingVoteReconciliation` — Per-class sold units and before/after owned units balance.
- **E04 [D]** `saleVolumeCannotIdentifyInstrumentClass` — Quantity does not determine ordinary versus super-voting security.
- **E05 [D]** `SettlementOwnershipWeld` — Exact synthetic funding/quantity/issuer/instrument label agreement.
- **E06 [D]** `shareClassTransferPreservesIssuedSupply` — Seller/buyer/treasury/issuance/cancellation legal share changes.
- **E07 [N]** `authenticatedOwnerIssuerInstrumentClassKey` — Evidence-checked beneficial owner, issuer, security and class.
- **E08 [N]** `controllingVotesRequireVerifiedRightsAndAgreements` — Majority arithmetic does not determine effective legal control.
- **E09 [N]** `persistentTransactionIdentityCannotFollowFromValueOrDigest` — Local object identity, value equality, content hash and registry identity differ.

### F. Clearing and investor attribution (7)

- **F01 [D]** `ParticipantClearingBatch.netAccounting` — Finite gross sell/buy to net-receipt accounting.
- **F02 [D]** `netReceiptCannotRecoverGrossTurnover` — Net zero can hide offsetting gross activity.
- **F03 [D]** `investorAllocationsSumToParticipantObligation` — Broker/custodian allocations aggregate to participant totals.
- **F04 [D]** `deliveryVersusPaymentCashAndTitleCoMove` — Conditional securities/cash finality with correct settlement authority.
- **F05 [D]** `aggregateNetPositionsRespectGrossCashAndSecurityTotals` — Signed buy/sell/receive/pay variants with no silent cancellation.
- **F06 [N]** `participantNetStatementDoesNotIdentifyIndividualTaxpayer` — A net participant receipt is not an individual's payment trace.
- **F07 [N]** `actualSettlementFinalityRequiresOfficialReceipt` — Simulated close event cannot create authentic custody receipt.

### G. Physical capacity and care (7)

- **G01 [D]** `saleVolumeCannotDeterminePhysicalCapacity` — Existing finite distinct installed-machine example.
- **G02 [D]** `careCannotFactorThroughTaxReceipt` — Same tax cash does not fix care outcome.
- **G03 [R]** `AIEconomicUsefulWorkTimeSeriesExact and UnitEconomicsMarginExact` — Useful work and positive return do not follow from volume.
- **G04 [D]** `physicalCapitalStockFlowConservation` — Existing stock + commissioned - retired = next stock with time.
- **G05 [D]** `deliveredCareHoursBoundedByStaffAndEquipment` — Staff time, buildings and equipment constrain care capacity.
- **G06 [N]** `energyMaterialsAndConstructionFeasibility` — Installed productive output consumes time and physical inputs.
- **G07 [N]** `financialClaimChangeDoesNotIdentifyPhysicalOutput` — Generic conditional non-factorability rather than physical law.

### H. Attribution, evidence and theorem authority (8)

- **H01 [R]** `AttributedSourceCore.citationImportsProofIsFalse` — External citation does not discharge kernel theorem.
- **H02 [R]** `SourceAttributionPromotionBoundaryExact.sameContentDoesNotAutoPromoteToIndependentProducer` — Reprints and summaries do not create independent sources.
- **H03 [R]** `EvidenceHyperfabricExact and SnowballAttributionProvenanceInvariantExact` — Preserve independent evidence fibres and genealogy.
- **H04 [R]** `ContentAddressedTransitionIdentityExact.canonicalTransitionIdentityBoundary` — Digest is not event identity/collision-freedom.
- **H05 [D]** `toePaperCannotSupplyKernelCertification` — Agda source and publication are not compiler receipts.
- **H06 [N]** `authorAndProofOwnershipAreDisjointReceiptTypes` — Original study, repository theorem, code, executed tests, Agda kernel all typed differently.
- **H07 [N]** `originalSourceProducerIsNotDerivedSummary` — Primary and derivative reports never become two independent observations.
- **H08 [N]** `measuredPolicyEffectRequiresSameObjectInputs` — Conditional matched person/security/tax/payment/time/outcome promotion.

### I. Pareto comparison and causal humility (9)

- **I01 [N]** `rivalPolicyTaxBasesRemainComparableButDistinct` — Compare wealth/income/inheritance/gains/land/vacancy on typed metrics.
- **I02 [N]** `policyScenarioRequiresStatuteOrHypotheticalTag` — Hypothetical hard cap not mislabeled enacted.
- **I03 [N]** `finitePolicyStateTransitionPreservesAccounting` — Across-period wealth/debt/security/care stocks balance.
- **I04 [N]** `behaviouralResponseParametersAreExplicitAssumptions` — Migration, credit and investor behaviour are not given theorems.
- **I05 [N]** `sameInitialStateDifferentInterventionComparison` — Explicit baseline and treatment labels.
- **I06 [D]** `paretoDominancePreorder` — Reflexive and transitive objective-vector comparison.
- **I07 [N]** `finiteParetoFrontierIsNonempty` — Nonempty finite feasible choice set has non-dominated element.
- **I08 [N]** `noUniqueOptimalTaxRateFromParetoOrderAlone` — Partial ordering does not select welfare weights.
- **I09 [N]** `syntheticModelCannotIdentifyObservedCausalEffect` — Separate case-study, controls and causal identification receipts.

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
