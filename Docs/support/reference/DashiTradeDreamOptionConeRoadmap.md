# dashiTRADE dream formalism: relational option-cone controller

Status: **reference architecture / roadmap, not a claim of current runtime conformance**.

This note records the architecture that the historical `dashiTRADE` implementation appears to have been reaching toward when read against the current DASHI theorem stack. It is intended to guide future consolidation without rewriting the runtime around a new metaphor or treating existing scalar gates as stronger certificates than they are.

The compact design principle is:

> **Trade only when an admissible action robustly dominates no trade, under the joint market/portfolio/execution state and with future option loss included in the trajectory cost.**

The primary object is therefore not BUY/HOLD/SELL as a ternary algebra. It is the **reachable/admissible action subfabric** at the current state.

---

## 1. Existing trading predecessor

`DASHI/Trading/PermissionKernel.agda` remains the historical Agda owner. It already separates five market coordinates:

- shape,
- energy,
- persistence,
- liquidity,
- risk,

before producing `ACT`, `HOLD`, or `BAN`.

That is important prior art: the trading model was already trying to avoid a single scalar signal.

However, the current `permissionKernel` only updates the permission coordinate. Its `tradingAction = modelCost + residualCost + riskPenalty` is unchanged by the kernel, so the existing non-increase receipt is a static equality witness rather than a theorem that an executed trade reduces economic action/cost.

`DASHI/Trading/DashiTradeDreamOptionConeExact.agda` therefore extends the *architecture*, not the authority of that theorem.

---

## 2. Current dashiTRADE runtime audit

The Python implementation currently contains several partially overlapping architectures.

### Legacy ternary controller

`ternary.py::ternary_controller(direction, edge, permission, capital_pressure, thesis)` appears five-dimensional, but operationally simplifies to approximately

```text
action = direction
iff permission = +1 and edge = direction != 0
otherwise HOLD/flat.
```

`thesis` is unused by the controller, and `capital_pressure` cannot block an otherwise permitted action because its blocking condition applies only when permission is not `+1`.

This is a syntactic product whose executable interaction geometry is much thinner than its argument list suggests.

### Newer `TriadicStrategy`

`strategy/triadic_strategy.py` is substantially closer to mature DASHI semantics:

- `FLAT` is intentional neutralization;
- `UNKNOWN` is normally epistemic suspension/hold;
- `PARADOX` or hard scaffolding failure produces hard closure;
- `OBSERVE` and `UNWIND` are distinct postures;
- hysteresis separates enter/leave thresholds.

The main remaining collapse is `confidence`:

```text
confidence
  -> permission/hysteresis
  -> target exposure multiplier
  -> urgency multiplier.
```

The dream formalism does **not** assume that epistemic legitimacy, size capacity, and execution urgency are the same coordinate.

### Learner

`strategy/learner_adapter.py` produces a scalar legitimacy score `ell in [0,1]` from quotient-feature/regime deviation. This is a plausible coarse observer, but not yet an action-indexed economic certificate.

A central DASHI test is therefore:

```text
Q(x) = Q(y)
but Outcome(x,a) != Outcome(y,a)
=> action outcome does not factor through Q.
```

If such a witness exists, no better post-processing or learner operating only on `Q` can recover the lost distinction.

The current live `DecisionEngine` also constructs `TriadicStrategy` without a `confidence_fn`, so this learner is not presently authoritative for the main stream-daemon decision path.

### Thesis/history memory

`policy/thesis.py` is architecturally valuable. It retains direction, strength, age, cooldown and invalidation count and derives evidence coordinates `alpha`, `beta`, `rho` before applying persistence/no-flip logic.

This should be read as a **history-deformed transition law**, not merely a ternary vote. History can change which next actions are reachable or how costly they are without deleting those actions from the underlying carrier.

### Sizing

`execution/sizing.py` folds participation capacity, velocity, inverse-vol targeting, high-vol shrinkage, equity/risk limits, edge decay and risk headroom into one scalar cap.

That scalar is useful as a consumer, but should not be treated as the complete state. Liquidity capacity, risk permission, predicted weight, barrier and actionability remain conceptually distinct.

### Cost gate

The stream daemon's `DecisionCostGate` is one of the strongest current pieces. It computes cost in coherent notional units:

```text
cost = |delta position| * price * (fee rate + slippage rate)
```

and permits exposure reduction asymmetrically. That is already close to a state-dependent action cone.

Its current expected-benefit model is still factorized:

```text
benefit
  = |delta position| * price
  * edge_bps
  * actionability
  * urgency.
```

The dream formalism treats this multiplication as a **model hypothesis**, not a theorem: individually favourable marginals need not imply favourable joint actionability.

### Candidate proof objects

The stream daemon already produces `SupportProof`, `StructuralProof`, `CandidateProof` and `DecisionProof`, with an intent candidate and an always-admissible HOLD fallback.

This is excellent scaffolding for the target architecture. The semantic upgrade is from

```text
configured gates passed
```

to

```text
this particular action is admissible and robustly dominates no trade under a declared joint-state/cost model.
```

### Accounting boundary

The legacy fill/accounting path should not yet be treated as a trusted net-edge observer. `apply_execution()` computes a fee separately from cash, while `compute_step_accounting()` subtracts the current fee from current PnL; this can make fee treatment path-dependent in unintended ways. The legacy fee formula also lacks price/notional if `cost` is intended to be a proportional rate.

Before PnL/edge feedback becomes promotion authority, units and cumulative cost accounting need a single canonical owner.

---

## 3. DASHI theorem alignment

### Intersectional non-factorability — PR #620

`DASHI.Core.IntersectionalNonFactorability` owns the generic fact:

```text
same coarse observer
+ different downstream outcome
=> no factorization through the coarse observer.
```

It also proves that arbitrary post-composition/recharting of the already-collapsed observer cannot recover the erased distinction.

Trading consequence:

```text
same direction/qfeature score
+ different BUY viability
=> direction/qfeature score is not sufficient for BUY viability.
```

The new trading Agda contains an exact same-long-direction witness with different BUY availability caused by inventory context.

### Nonlinear intersection — PR #620

`IntersectionalConstraintGeometryExact` proves a finite interaction pattern in which each marginal remains open while the joint configuration closes the selected affordance.

Trading consequence:

```text
signal good
liquidity marginal good
risk marginal good
!= theorem that joint trade is good.
```

Interaction terms are first-class model obligations.

### Hyperfabric / reachable subfabric — PR #606

PR #606 separates

```text
world possibility
!= perceived possibility
!= accessible possibility
!= actionability
```

and separately types predicted weight, accessibility, barrier and actionability on a branch.

Trading interpretation:

```text
trade exists in action vocabulary
!= model proposes it
!= portfolio/execution context permits it
!= it clears the current barrier
!= it is authorized now.
```

An unavailable trade is not deleted from the underlying action carrier.

`DashiTradeDreamOptionConeExact` carries an application-level finite shadow of these fields while deliberately leaving #606 as the eventual generic owner after branch ancestry is reconciled.

### Relational affordance cone — PR #618

PR #618 models action availability as a relation over a person and a multi-coordinate ecology rather than as a property of the person alone.

The trading analogue is:

```text
availableTrade : PortfolioState -> MarketEcology -> TradeAction -> Set
```

where `MarketEcology` may include microstructure, volatility regime, venue/rules, cross-asset state, execution state and retained history.

The key lesson is relational: the same proposal can inhabit different reachable option cones under different contexts.

### History-valued action — PR #606

PR #606 also proves that two routes with the same endpoints can have different trajectory costs.

Trading should therefore admit costs such as

```text
fees + slippage + impact + risk + turnover + future optionality loss.
```

Positive endpoint PnL alone is not a theorem of a good trajectory.

---

## 4. Dream state and action geometry

A target state should remain a product rather than immediately collapsing to one score:

```text
S_t = (
  market observation,
  retained history,
  quotient/representation state,
  inventory/portfolio state,
  uncertainty/calibration state,
  risk/capability state,
  execution/microstructure state
).
```

A directional model may propose

```text
d_t = D(S_t) in {SELL, FLAT, BUY}
```

but `d_t` is an observer/proposal, not an authorization.

For each candidate action `a`, construct a branch profile such as

```text
B_t(a) = (
  physical possibility,
  predicted value/weight,
  accessibility,
  barrier,
  actionability
).
```

Then define the current option cone

```text
C_t = { a | Available(S_t,a) }.
```

No trade/HOLD should remain a first-class safe candidate:

```text
HOLD in C_t.
```

Only after the cone is constructed should an optimizer choose among its members.

---

## 5. Action-indexed economic certificate

A candidate certificate should be indexed by the action, not one scalar reused for all actions:

```text
Gamma_t(a) = (
  expected gross edge,
  uncertainty/calibration bound,
  execution-cost bound,
  risk/capability state,
  support/OOD state,
  persistence/history state,
  future-option effect
).
```

One robust admission pattern is:

```text
lower_bound_gross_edge(a)
  > upper_bound_execution_cost(a)
    + risk_margin(a)
    + optionality_margin(a)
```

plus the non-economic safety/capability requirements.

Prediction confidence remains distinct from economic edge:

```text
confidence != edge magnitude != cost != risk capacity != urgency.
```

---

## 6. Trajectory optimization

Once `C_t` is known, a short-horizon consumer can compare candidate trajectories:

```text
J(gamma_a)
  = expected return
  - execution cost
  - risk cost
  - turnover/path cost
  - future optionality loss.
```

A receding-horizon/MPC implementation is one possible consumer of this geometry, not the ontology itself.

The control principle is:

```text
choose a* in C_t maximizing J(gamma_a)
```

with HOLD/no-trade winning whenever no admissible action robustly dominates it.

---

## 7. Representation refinement loop

The dream architecture should make observer failure productive.

For an observer `Q` and action `a`, search explicitly for

```text
Q(x) = Q(y)
but V(x,a) != V(y,a).
```

Such a witness is not merely “bad model accuracy.” It is evidence that the declared action-relevant phenomenon does not descend through `Q`.

The correct response is to refine the observer/carrier with the missing residual coordinate, then re-test sufficiency. Reweighting or relabelling the same collapsed quotient is not enough.

---

## 8. Runtime consolidation roadmap

### R0 — freeze semantic vocabulary

Keep distinct:

```text
proposal/direction
prediction/weight
uncertainty
permission
accessibility
barrier/cost
risk capability
actionability
urgency
size
history/thesis
execution
realized outcome
```

Do not encode `UNKNOWN` and `PARADOX` as ordinary numerical trits adjacent to BUY/FLAT/SELL.

### R1 — canonical decision path

Choose one authoritative runtime path. Today the legacy loop and stream-daemon path implement materially different semantics.

Document which path owns live decisions and treat the other as compatibility/regression code until intentionally retired.

### R2 — canonical observer contract

Name each observer and its consumer:

```text
proposal observer
admission observer
cost observer
risk observer
outcome/accounting observer.
```

Unify the two incompatible six-dimensional quotient-feature definitions or explicitly type them as different observers; equal vector dimension is not semantic equivalence.

### R3 — accounting/unit normalization

Give fees, spread, slippage, impact, edge and PnL one canonical unit convention.

Do not compare dollar-per-unit edge to dimensionless cost rates.

### R4 — action-indexed certificates

Replace global `confidence -> permission/size/urgency` authority with action-indexed certificate fields. Confidence may remain one input.

### R5 — relational option cone

Compute action availability from the joint state. Treat independent/multiplicative gate composition as a hypothesis requiring regression witnesses.

### R6 — history and future optionality

Retain thesis/history as transition deformation. Add trajectory/path cost and future-option loss to candidate comparison.

### R7 — robust dominance over no trade

Make the decision proof certify a declared robust net-edge proposition rather than only a list of passed gates.

### R8 — representation counterexample harness

Continuously search for same-observer/different-action-outcome witnesses. Promote discovered residuals into candidate observer refinements instead of only retraining post-processors.

### R9 — parity and implementation receipt

For each production decision path, emit a receipt connecting:

```text
raw state
-> observer values
-> candidate set
-> per-action certificates
-> option cone
-> chosen trajectory
-> execution
-> realized accounting outcome.
```

Only then claim runtime conformance to the dream formalism.

---

## 9. Current Agda boundary

`DASHI/Trading/DashiTradeDreamOptionConeExact.agda` currently proves only finite structural facts:

- HOLD is always available in the finite specimen;
- same long-direction proposal can hide different BUY viability;
- BUY viability therefore does not factor through direction alone;
- arbitrary post-processing of direction still cannot recover that erased viability;
- equal predicted weight need not imply equal accessibility;
- accessibility need not equal actionability;
- favourable declared marginals do not force joint BUY availability;
- two schematic trade trajectories can share the same endpoint role while carrying different total path costs.

It explicitly records as false/uninhabited claims that:

```text
legacy PermissionKernel = complete dream architecture
scalar confidence determines authorization, size and urgency
marginal gate success implies joint trade viability
current CandidateProof already proves robust economic dominance
current Python runtime conformance is supplied.
```

This is intentional. The file is a theorem-bearing roadmap boundary, not retroactive verification of dashiTRADE.

---

## 10. Intended eventual composition

After draft ancestry is reconciled, the desired ownership graph is:

```text
PermissionKernel                    historical trading predecessor
IntersectionalNonFactorability      erased-coordinate / no-rechart theorem
#606 reachable-subfabric owners     possibility/access/barrier/actionability
#618 relational affordance owner    joint-context action availability pattern
Trading adapter                     market/portfolio instantiation only
Runtime receipt                     dashiTRADE implementation conformance
```

The trading domain should become mostly an instantiation of generic DASHI owners, not a second private theory of observers, hyperfabrics, reachability or interaction.
