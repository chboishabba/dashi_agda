# LES research cross-pollination and gap map

## Status

This note maps the current LES/DASHI planning spine onto nearby research literatures and, equally importantly, records what those comparisons **do not yet discharge**.

The corresponding exact Agda carrier is:

- `DASHI.Environment.LESResearchCrossPollinationExact`

The literature is used as motivation and a source of proof techniques. It is not treated as proof authority for DASHI's exact formulations.

---

## 1. Behaviourally safe latent compression

### Existing DASHI content

`DASHI.Core.DynamicalQuotientSafety` already asks a stronger question than present-time reconstruction error: if two concrete states are identified by a projection now, do their projected observations remain equal after every declared future action trace?

`DASHI.Core.GenericFuturePartitionRefinementExact` supplies the finite-depth version and trace observation theorem. `TerminalisationDefect` supplies a concrete witness that a present-time quotient is dynamically unsafe. `ReopeningScheme` supplies the independent route of retaining enough residual/provenance information to reconstruct the fine state.

### Literature anchor

Norman Ferns, Prakash Panangaden, Doina Precup, **“Metrics for Finite Markov Decision Processes”**, UAI 2004, pp. 162–169; continuous-state extension: **“Bisimulation Metrics for Continuous Markov Decision Processes”**, *SIAM Journal on Computing* 40(6), 2011, 1662–1714, DOI `10.1137/10080484X`.

The literature supplies a probabilistic/metric state-similarity framework and value-function error bounds. DASHI's existing trace congruence is deterministic and exact; the new `ApproximateFutureMetricContract` adds a deliberately modest metric propagation theorem without pretending to reproduce the full MDP result.

### Formal addition

The new module proves:

```text
stateDistance x y <= epsilon
+ every declared action preserves epsilon-closeness
=> every finite action trace preserves epsilon-closeness
=> terminal observations remain epsilon-close.
```

This is a usable bridge from exact `DynamicConsumerSafety` toward bisimulation-metric-style approximate abstraction.

### Still missing

- stochastic transition kernels and probability metrics;
- reward/value-function preservation bounds;
- policy-relative/on-policy abstractions;
- continuous state spaces and measurable structure;
- empirical certification that a learned GLES encoder satisfies the metric contract.

---

## 2. Decision-relevant compression and sufficiency

### Literature anchor

Yann Dubois, Benjamin Bloem-Reddy, Karen Ullrich, Chris J. Maddison, **“Lossy Compression for Lossless Prediction”**, NeurIPS 2021, arXiv `2106.10800`.

That work characterises compression for downstream predictive task classes. It is a useful mathematical neighbour of DASHI's consumer-relative projection logic, but it does **not** establish the stronger future-dynamical safety property by itself.

### Formal addition

`TaskFactorisation` requires every declared task to factor exactly through the compressed representation:

```text
evaluate task state = evaluateReduced task (project state).
```

From equality of compressed states we prove equality of every declared task output.

`CompressionAdmission` then makes two acceptable routes explicit:

1. dynamic future safety; or
2. exact task sufficiency **plus** an exact reopening scheme.

This preserves the existing DASHI warning that static sufficiency and dynamic safety are independent obligations.

### Still missing

- rate-distortion functions and actual bit/complexity budgets;
- probabilistic sufficient statistics;
- task-family completeness: who decides which future consumers count?;
- computational cost of reopenability and residual storage;
- privacy, access-control, and retention constraints on residual information.

---

## 3. Path A -> B -> C and multi-fidelity optimisation

### Literature anchor

Natalia M. Alexandrov, J. E. Dennis Jr., Robert M. Lewis, Virginia Torczon, **“A trust-region framework for managing the use of approximation models in optimization”**, *Structural Optimization* 15 (1998), 16–23, DOI `10.1007/BF01197433`.

The important lesson is local model-management with explicit high/low-fidelity agreement, not a claim that every LES fidelity lane forms a simple ordered mesh hierarchy.

### Formal addition

`FidelityAgreementReceipt` records:

- low/high model identities;
- the region in which they were compared;
- an agreement statistic and threshold;
- a proof the statistic is within threshold;
- the local consistency method and evidence.

`TrustRegionEscalationReceipt` ties this to the existing `SurrogateAssessment` and the exact A/B/C `chooseLane` rule.

### Still missing

- convergence theorems for actual LES optimisers;
- trust-region radius update mathematics;
- first-order/gradient consistency where available;
- heterogeneous non-ordered fidelities;
- cost-aware fidelity allocation;
- asynchronous and batched high-fidelity evaluation;
- coupled fidelity choices across hydrology, ecology, economics and infrastructure.

---

## 4. Hard conservation rather than soft physics penalties

### Literature anchor

Anthony Baez, Wang Zhang, Ziwen Ma, Subhro Das, Lam M. Nguyen, Luca Daniel, **“Guaranteeing Conservation Laws with Projection in Physics-Informed Neural Networks”**, NeurIPS 2024, arXiv `2410.17445`.

The numerical lesson is directly relevant: a soft physics-informed loss is not itself a guarantee of conservation; a projection can instead force the output onto a conservation manifold.

### Formal addition

`HardInvariantProjection` requires the projection result to inhabit the declared invariant for every input state. `ConservationProjectionReceipt` separates the formal conservation bundle from the numerical projection method and evidence.

This complements, rather than replaces, `DASHI.Environment.QuantitiesConservation`.

### Still missing

Conservation is necessary but not sufficient for physical adequacy. LES still needs domain-specific gates for, where relevant:

- positivity and boundedness;
- entropy/dissipation inequalities;
- stability and monotonicity;
- maximum principles;
- constitutive admissibility;
- stoichiometric and charge/electroneutrality constraints;
- discretisation-induced conservation error;
- coupled conservation across model boundaries.

---

## 5. Pareto planning and post-front decision support

### Literature anchor

Maureen C. Kennedy, E. David Ford, Peter Singleton, Mark A. Finney, James K. Agee, **“Informed multi-objective decision-making in environmental management using Pareto optimality”**, *Journal of Applied Ecology* 45 (2008), 181–192, DOI `10.1111/j.1365-2664.2007.01367.x`.

The paper supports the existing LES/DASHI separation between visible multi-objective trade-offs and scalar weighted collapse.

### Formal addition

`ParetoInterpretationReceipt` keeps front generation separate from:

- front distillation/clustering;
- stakeholder preference models;
- final plan choice.

It explicitly refuses to infer a unique optimum from non-dominance.

### Research gap the original mapping missed

**Pareto generation is not decision completion.** Environmental MCDA has a large literature on preference elicitation and stakeholder participation. A 2011 review of more than 300 environmental MCDA papers emphasises the need to combine technical evidence with stakeholder values (Huang, Keisler & Linkov, *Science of the Total Environment*, DOI `10.1016/j.scitotenv.2011.06.022`). Recent human-in-the-loop reviews likewise find that reproducible selection from Pareto fronts remains much weaker than front generation.

LES therefore still needs a first-class, provenance-bearing theory of preference elicitation, disagreement, sensitivity and legitimate aggregation rather than treating “human review” as an opaque terminal step.

---

## 6. Approval provenance versus governance legitimacy

### Existing DASHI content

`DASHI.Environment.ValidationGovernance` already separates model validation from ecological, engineering, policy, legal and community approval.

### Formal addition

`ApprovalEvent` replaces a detached approval Boolean with an action-bound event carrying:

- governed action hash;
- authority identity and role;
- timestamp;
- scope;
- evidence artifact hash;
- approval state;
- revocation reference.

`DeploymentApprovalWitness` requires an explicit proof that the event is approved and separately records scope, current authority and revocation checks.

### Research gap the original mapping missed

Cryptographic/provenance integrity does **not** establish legitimacy. LES still lacks formal accounts of:

- who is authorised to approve what;
- consent and withdrawal;
- contestability and appeal;
- conflicting jurisdictions;
- community/custodian authority that is not reducible to institutional signatures;
- revocation after deployment;
- temporal expiry of an approval;
- procedural fairness.

The formal module records this boundary explicitly.

---

# Research gaps missed by the five-thread mapping

The external references in the prompt are useful, but they leave several theorem-sized research programmes uncovered. These are now recorded explicitly in `LESResearchGapBoundary`.

## A. Partial observability and belief-state safety

The current DASHI future-safety theory starts from a `State` and deterministic action transition. Real LES operation rarely observes the true ecological/hydrological state directly.

Modern POMDP representation work makes the distinction explicit. For example:

- Guo et al., **“Provably Efficient Representation Learning with Tractable Planning in Low-Rank POMDP”**, ICML 2023;
- Zhang et al., **“Provable Representation with Efficient Planning for Partially Observable Reinforcement Learning”**, ICML 2024.

LES therefore needs:

```text
observation history -> belief / sufficient predictive state -> decision
```

and a safety theorem on beliefs or predictive states, not only on fully observed states.

This is one of the highest-priority missing mathematical layers.

## B. Causal abstraction, not only behavioural abstraction

Bisimulation-style equality says two states behave similarly under a declared transition/action semantics. It does not automatically prove that an abstraction preserves **causal intervention semantics**, confounding structure or counterfactual queries.

That matters directly for LES inverse questions such as “did upstream fertiliser application cause this load?” and intervention transfer such as “will this buffer work if deployed here?”.

The repo needs a causal-abstraction/intervention-preservation layer distinguishing:

```text
prediction equivalence
!= intervention equivalence
!= counterfactual equivalence.
```

Recent causal-MDP and causal-abstraction work provides candidate machinery, but this is not yet in the LES spine.

## C. Structural identifiability and environmental equifinality

`InversePlanning` ranks admissible explanations, but it does not yet prove when source parameters or mechanisms are identifiable from the observations.

Keith Beven's **“A manifesto for the equifinality thesis”**, *Journal of Hydrology* 320 (2006), 18–36, DOI `10.1016/j.jhydrol.2005.07.007`, is directly relevant: multiple model structures or parameter sets can remain observationally acceptable.

LES needs explicit carriers for:

- identifiable / non-identifiable parameters;
- observational equivalence classes;
- alternative model structures;
- profile/posterior uncertainty;
- source-attribution non-uniqueness;
- experiment or measurement sets that break the equivalence.

Without this, an MDL-minimum explanation can still look more determinate than the evidence warrants.

## D. Value of information and active sensing

The current architecture can expose missing data, but it does not yet solve the next decision:

> Which measurement should we buy next, and is it worth more than acting now?

Williams, Eaton & Breininger, **“Adaptive resource management and the value of information”**, *Ecological Modelling* 222 (2011), 3429–3436, DOI `10.1016/j.ecolmodel.2011.07.003`, gives the natural-resource-management version of this problem.

LES should eventually optimise jointly over management actions and information-gathering actions:

```text
measure / sample / inspect / simulate / act / wait.
```

This is especially important for pollution source attribution, threatened species, soil sampling and expensive Path-C runs.

## E. Deep uncertainty and robustness across plausible futures

Pareto optimisation over one declared scenario family is weaker than robust decision support when probabilities, models or stakeholder preferences are themselves contested.

Decision-Making under Deep Uncertainty literature explicitly shifts emphasis from “best prediction” to plans that remain acceptable across many plausible futures.

LES needs a robust/adaptive-pathway layer for:

- climate regime uncertainty;
- model-form uncertainty;
- price/market uncertainty;
- policy change;
- irreversible actions;
- signposts that trigger plan revision;
- regret/satisficing/robustness metrics across scenario ensembles.

This is not supplied by ordinary Pareto dominance or A/B/C fidelity escalation.

## F. Non-stationarity and distribution shift

The present surrogate contract records declared training support, which is good, but the mathematical object is essentially static.

Living environments drift:

- climate distributions change;
- species ranges move;
- management changes soil and hydrology;
- sensors age;
- policy and market regimes change.

LES therefore needs time-indexed support and calibration validity, shift detection, expiration/revalidation rules and possibly conformal or other finite-sample coverage methods under clearly stated assumptions.

## G. Online data assimilation and model revision

A living-environment system should not remain a batch planner after deployment. Earth-system digital-twin literature treats data assimilation as a key mechanism for continually aligning model state with observations.

Luo et al., **“Ecological forecasting and data assimilation in a data-rich era”**, *Ecological Applications* (2011), DOI `10.1890/09-1275.1`, is an established ecological anchor; recent Earth-system digital-twin reviews make the same point at much larger scale.

LES needs typed update operations for:

```text
prior state + new observation -> posterior/revised state
```

with provenance, uncertainty contraction/expansion, and invalidation of dependent plans and receipts.

## H. Spatial scale, aggregation and the MAUP

`SpatialTransport` is strong on typed connectivity, but it does not yet protect against the fact that statistical and planning conclusions can change when spatial cells or zones are redefined.

Michael Goodchild, **“Scale in GIS: An overview”**, *Geomorphology* 130 (2011), 5–9, DOI `10.1016/j.geomorph.2010.10.004`, explicitly discusses resolution, extent, cross-scale inference, the modifiable areal unit problem and ecological fallacy.

LES needs spatial refinement/coarsening laws saying which quantities and conclusions commute with aggregation and which require residual information. This connects almost perfectly to the existing DASHI quotient/descent machinery and should be a high-alpha cross-pollination target.

## I. Cross-model uncertainty propagation

The current receipt structure can attach uncertainty to individual models, but coupled environmental planning needs uncertainty transported through a **network of models**.

Errors are often correlated because models share:

- meteorological inputs;
- DEMs;
- soil maps;
- calibration observations;
- structural assumptions.

Treating model uncertainties as independent can therefore badly understate system uncertainty. LES needs a dependency-aware covariance/error-budget or imprecise-probability carrier and consumer-local aggregation rules.

This is a direct application area for DASHI's recent local-vs-global residual and consumer-indexed relevance results.

## J. Continuous-time, hybrid dynamics and path dependence

The current generic DASHI action system is an excellent finite trace semantics, but environmental systems contain:

- continuous flows;
- discrete interventions;
- threshold events;
- hysteresis;
- delayed responses;
- irreversible transitions.

A useful LES semantics will eventually need continuous-time or hybrid-system refinement and an explicit history/path carrier for systems where current state summaries are not Markov-sufficient.

Examples include soil compaction, ecological succession, seed banks, groundwater memory and regime shifts.

## K. Search completeness and computational guarantees

Finite Pareto correctness is not the same as complete candidate generation. LES still needs to distinguish:

```text
non-dominated among generated candidates
```

from

```text
non-dominated in the full admissible intervention language.
```

The newer generic DASHI future-partition stabilization and certified finite quotient machinery may provide a route for bounded intervention languages, but this has not yet been instantiated for LES planning search.

## L. Socio-ecological feedback and strategic agents

The present world model treats many economic/community constraints as inputs. In actual land and water management, people adapt to the plan:

- landholders change behaviour;
- markets respond;
- enforcement changes incentives;
- neighbouring interventions interact;
- collective-action problems arise.

That requires dynamic socio-economic or game-theoretic agents rather than static costs and constraints. This is outside the current LES formal spine.

---

# Priority order

For the next research/formalisation round, the highest-alpha sequence is:

1. **Partial-observation / belief-state future safety.** Without this, the present exact state abstraction theory assumes more observability than field systems actually have.
2. **Causal intervention-preserving abstraction + identifiability/equifinality.** This directly governs inverse diagnosis and whether intervention recommendations transfer.
3. **Value of information / active sensing.** This turns “missing evidence” into a decision about what to measure next.
4. **Deep-uncertainty robustness + adaptive pathways.** This is necessary for climate-scale and long-horizon deployment.
5. **Spatial scale/MAUP descent theorems.** This is an unusually good fit to DASHI's existing quotient/intertwining machinery.
6. **Online assimilation and receipt invalidation/reopening.** This makes LES genuinely living rather than a static planner.
7. **Dependency-aware cross-model uncertainty propagation.** Especially important once multiple authoritative adapters are coupled.
8. **Continuous-time/hybrid/path-dependent semantics.** Necessary for physical realism after the finite planning language is stable.
9. **Preference elicitation and procedural governance.** Pareto and signed receipts are necessary but not a substitute for legitimate final choice.
10. **Search-completeness certificates for bounded intervention languages.** This can reuse the latest finite future-refinement/quotient compiler work.

---

# Resulting architectural thesis

The external literature strengthens, but also narrows, the correct claim for GLES:

```text
A reduced environmental state is admissible only relative to declared consumers,
future dynamics, task families, uncertainty regimes and governance scope.
```

The stronger long-term target is therefore not merely:

```text
compress -> predict -> optimise.
```

It is:

```text
observe under partial information
-> maintain a reopenable belief/world state
-> compress relative to declared consumers
-> preserve causal and dynamical queries needed by those consumers
-> propagate physical and epistemic constraints
-> search robust intervention portfolios
-> decide whether to act or acquire more information
-> escalate fidelity where evidence requires it
-> obtain scoped, contestable approval
-> act
-> assimilate outcomes and reopen/revise dependent conclusions.
```

That is a materially larger research programme than the original five literature anchors, and the gap list is now explicit rather than silently absorbed into generic “uncertainty” or “human review” fields.
