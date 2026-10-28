# Wealth-tax × dashiTRADE: exact completion roadmap and scoped lemma ledger

Created 2026-10-28. **77 named formal obligations** across nine groups: 28 already source-written (D), 9 owned by existing reusable sources (R), 40 new required proofs/contracts (N). D and R are NOT equivalent to an observed Agda kernel pass. N are *proposed names*, not already implemented.

Source PRs: [dashi_agda #1277](https://github.com/chboishabba/dashi_agda/pull/1277); [dashiTRADE #3](https://github.com/chboishabba/dashiTRADE/pull/3). This ledger defines the complete finite scope **for this economics/trade research release**; it is not a finite list of all possible theorems in macroeconomics or physics. Reuse first; do not edit ESD or overwrite diverged TOE root files.

## Formal lemma and record obligations

### A. Tax base and assessment-day ceiling (8)

- **A01 [D]** `incomeTaxIsNotStockCap` — Stock and annual income taxes are distinct constructors.
- **A02 [D]** `vacancyTaxIsNotWealthCap and inheritanceTaxIsNotAnnualWealthLevy` — Different legal tax bases remain typed.
- **A03 [D]** `sourceAIProposedRatesAreNotVictoriaLaw` — AI-suggested 1/2/5% idle equity is not the enacted Victoria VRLT schedule.
- **A04 [D]** `annualSnapshotIsNotContinuousBound` — Assessment-time cap does not bound all between-assessment states.
- **A05 [N]** `netWealthBalanceIsWellTyped` — One timestamp and unit, with debt and beneficial-ownership exclusions.
- **A06 [N]** `netWealthAfterFullyPaidExcessEqualsMin` — Given full collection, after-payment wealth equals min(W,K).
- **A07 [N]** `hundredPercentLiabilityZeroBelowThreshold` — Generic threshold/truncated subtraction cases.
- **A08 [N]** `wealthLiabilityMonotoneAndThresholdBounded` — General fixed-threshold monotonicity and upper bound.

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
- **C07 [N]** `loanProceedsIncreaseLiabilities` — Borrowed proceeds create offsetting debt.
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
- **D09 [N]** `genericExecutedCountBoundedBySubmitted` — Finite list of fills cannot exceed authorized order under contract.
- **D10 [N]** `genericSettledCountBoundedByExecuted` — All partial fills and unsettled remainders balance.
- **D11 [N]** `genericSettledProceedsIsExactPriceQuantitySum` — Arbitrary number of exact fills, no ambient decimal rounding.
- **D12 [N]** `uniqueFillIdentityAndMonotoneEventTime` — Unique IDs, instrument and 4-stage timestamp agreement.

### E. Share class and control identity (9)

- **E01 [D]** `ownerWeightedVotes and afterTransferVotesRemainAboveHalf` — Finite super-vote example.
- **E02 [D]** `quantityCannotFixVotingControl` — Same sale count can leave 34/50 versus 16/50 voting power.
- **E03 [D]** `FundingVoteReconciliation` — Per-class sold units and before/after owned units balance.
- **E04 [D]** `saleVolumeCannotIdentifyInstrumentClass` — Quantity does not determine ordinary versus super-voting security.
- **E05 [D]** `SettlementOwnershipWeld` — Exact synthetic funding/quantity/issuer/instrument label agreement.
- **E06 [N]** `shareClassTransferPreservesIssuedSupply` — Seller/buyer/treasury/issuance/cancellation legal share changes.
- **E07 [N]** `authenticatedOwnerIssuerInstrumentClassKey` — Evidence-checked beneficial owner, issuer, security and class.
- **E08 [N]** `controllingVotesRequireVerifiedRightsAndAgreements` — Majority arithmetic does not determine effective legal control.
- **E09 [N]** `persistentTransactionIdentityCannotFollowFromValueOrDigest` — Local object identity, value equality, content hash and registry identity differ.

### F. Clearing and investor attribution (7)

- **F01 [D]** `ParticipantClearingBatch.netAccounting` — Finite gross sell/buy to net-receipt accounting.
- **F02 [D]** `netReceiptCannotRecoverGrossTurnover` — Net zero can hide offsetting gross activity.
- **F03 [N]** `investorAllocationsSumToParticipantObligation` — Broker/custodian allocations aggregate to participant totals.
- **F04 [N]** `deliveryVersusPaymentCashAndTitleCoMove` — Conditional securities/cash finality with correct settlement authority.
- **F05 [N]** `aggregateNetPositionsRespectGrossCashAndSecurityTotals` — Signed buy/sell/receive/pay variants with no silent cancellation.
- **F06 [N]** `participantNetStatementDoesNotIdentifyIndividualTaxpayer` — A net participant receipt is not an individual's payment trace.
- **F07 [N]** `actualSettlementFinalityRequiresOfficialReceipt` — Simulated close event cannot create authentic custody receipt.

### G. Physical capacity and care (7)

- **G01 [D]** `saleVolumeCannotDeterminePhysicalCapacity` — Existing finite distinct installed-machine example.
- **G02 [D]** `careCannotFactorThroughTaxReceipt` — Same tax cash does not fix care outcome.
- **G03 [R]** `AIEconomicUsefulWorkTimeSeriesExact and UnitEconomicsMarginExact` — Useful work and positive return do not follow from volume.
- **G04 [N]** `physicalCapitalStockFlowConservation` — Existing stock + commissioned - retired = next stock with time.
- **G05 [N]** `deliveredCareHoursBoundedByStaffAndEquipment` — Staff time, buildings and equipment constrain care capacity.
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
- **I06 [N]** `paretoDominancePreorder` — Reflexive and transitive objective-vector comparison.
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
