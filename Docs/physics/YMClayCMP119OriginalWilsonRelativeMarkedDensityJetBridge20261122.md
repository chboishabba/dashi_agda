# YM P0 — CMP119 original-Wilson relative marked-density jet bridge (22 November 2026)

**Status:** exact algebraic comparison lemma, local 144/144 rational diagnostic; no SU(N) physical RG approximation majorant, no W3, no Agda kernel or CI.

## Source audit / exact first uninhabited boundary

- `BalabanCMP119Equation218FactorizedFunctionalDensityExact.agda` carries source-shaped (2.18) sequence sums, (2.19) component products, and (2.20)/(2.22) ordered T-step products. The explicitly named `literalCMP119Equation218IndexExtractionLevel`, `literalCMP119Equation219ComponentExtractionLevel`, `literalCMP119Equation220StepExtractionLevel` are **conditional**. Merely constructing this record does not identify the actual original Wilson density and domain factors.
- `BalabanCMP119FactorizedMarkedBudgetVanishesExact.agda` proves a compiler from *assumed* per-step marked approximation-majorant vanishing to factorized density-error vanishing. It is not automatically a bound on the actual full-original Wilson mixed Hessian, its physical-distance dependence, or absolute differentiated cluster charges.
- `BalabanLiteralTwoWilsonSourceFirstJetLocalizationExact.agda` still marks `literalPointwiseWilsonJetLocalizationLevel` and `literalLocalizedWilsonShellChargeSumLevel` conditional.
- `BalabanLiteralTwoWilsonCMP116ConnectingTailExact.agda` identifies precisely `TwoWilsonCMP116PhysicalShellPayment.chargeSumBelowPhysicalRootedShell` as an external input after the connected-cluster algebra. Its absolute derivative sum argument assumes pointwise charge and a physical rooted-shell charge domination.
- Original #1536 `YMClayOriginalF19CMP119MarkedActionHessianTower20261122.md` already establishes finite true original Wilson coefficients and chain rule, including BOTH inherited Hessian and first-score covariance, not a physical CMP119 T-operation.

## Exact two-source relative-density log-jet comparison

For **positive** differentiable real marked densities K(s,t) and T(s,t) on the same specified original source domain, write

    Delta(s,t) = [K(s,t)-T(s,t)]/T(s,t),    K=T(1+Delta).

Then algebraic differentiation yields the exact identity

    D_st(log K-log T)
      = Delta_st/(1+Delta) - Delta_s Delta_t/(1+Delta)^2.

If throughout a chosen two-source square (and for each original source fibre/cutoff) |Delta|<=delta<1, |Delta_s|<=epsilon_s, |Delta_t|<=epsilon_t and |Delta_st|<=epsilon_st, then

    |D_st(log K-log T)|
      <= epsilon_st/(1-delta) + epsilon_s epsilon_t/(1-delta)^2.

This remains a **pointwise** error at fixed remaining slow field unless the comparison densities have already been integrated/normalized with their genuine Wilson reference measure. A pointwise log error cannot be silently promoted to a normalized global log partition error under different measures. The latter requires its own exact integration/reference-density and derivative argument.

Likewise, to get a physical W3 bound, each epsilon and any summed approximation-error contribution must have genuine source-supported **absolute localization**, not only convergence with refinement. A bound that vanishes at any fixed finite support but has uncontrolled support-count/volume prefactors is insufficient. Vanishing of Delta(s,t) at the source origin alone provides no derivative bound (e.g. Delta=st).

## R445/C3/TOE nonpromotion

C3 can permute the original link domains and derivative terms only when actual Wilson Haar/action, source marks, and candidate renormalized density are equivariant, and the compatibility map preserves original support and physical distance. A C3 symmetry reduces bookkeeping; it does not produce the per-step absolute epsilons, nor show Q_c(2a)=Q_f(a)^2. #1281 is downstream convergence consumer, #1291 indexed geometry/provenance consumer, #1217 realization graph remains conjectural; #1536 owns physical source.

## Executed local rational reference

`scripts/check_ym_cmp119_relative_marked_density_20261122.py`: 4 explicit positive bounded-mark probability laws, all 16 ordered original/comparison pairs, 9 affine rational source settings each = **144/144 exact rational checks**. Independently SymPy differentiated log K-log T and the Delta comparison formula; checked pointwise absolute triangle budget and strict positivity on |s|,|t|<=9/100 test grid, plus uniform affine source positivity and the Delta=st zero-at-origin/no-jet negative control. These are reference laws, NOT 4D SU(N) full Haar, real CMP119 action, or a renormalized cluster bound.

## Required next original physical payment

1. Select exact original F19 K(s,t) and CMP119/122 T(s,t) on the SAME correctly integrated slow-field/reference measure, with literal E/R/B/V sequence/step identification, 1/F/G/FG coefficient provenance and the inherited mixed action Hessian.
2. Derive pointwise or appropriately integrated absolute bounds for Delta, Delta_s, Delta_t, Delta_st from actual CMP119 physical step errors with genuine support geometry and source inflation. Do not replace these with mere Vanishes statements.
3. Propagate termwise, not signed, through the genuine marked connected activity/cluster log; bound absolute connecting sums with cutoff-uniform amplitude, physical-rate inf_a[-log Q(a)/a]>0 and all large-field/good-CMP116 discrepancies.
4. Only after those estimates, inhabit existing CMP116 physical W3 and original E1/D1/D2/N1/G1 recipients.

Attribution: original Wilson/Haar; Bałaban CMP119/122/116 and existing DASHI producers; elementary multivariable logarithmic differentiation. No new quantum field theorem.
