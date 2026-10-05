# LILA / Monster geometric-reasoning max-cut

This note records the cross-pollination implemented by the accompanying Agda and Lean owners. It is a DASHI synthesis layer. It does **not** transfer authorship between LILA, Sophontic, Monster-group sources, or DASHI.

## Claim grades

| Statement | Grade |
| --- | --- |
| LILA uses E8 geometry as an engineering prior | repository/source-facing engineering claim already tracked by the LILA provenance owners |
| Trialectic global T9 splits as a dyadic T4 local times a five-trit complement | existing formal theorem |
| The five-trit complement has 243 states | existing formal theorem |
| The canonical constant/diagonal locus has 3 states | new finite construction; Lean computes the subtype exactly |
| The non-diagonal T5 carrier has 240 states | new Lean finite theorem; Agda records the arithmetic seam but does not manufacture a separate finite-enumeration receipt |
| The non-diagonal T5 carrier **is** the E8 root system | **not proved**; requires explicit two-sided recognition and action intertwining |
| Monster 3A, 3B, 3C are interchangeable ternary labels | rejected; existing subgroup benchmark keeps them distinct |
| Monster 3B has an explicit finite Heisenberg/Schrodinger action | existing Agda theorem |
| Semantic interventions obey the Monster 3B action | **candidate empirical/model-recognition hypothesis only** |
| `t1=[C,DCD]^7` is source-paid | existing source receipt |
| t2 exact matrix / scalar orientation / q-word alignment is paid | **false/open** in the existing source frontier |
| Action-compression quality is a Sophontic metric | **false attribution**; the score surface in this tranche is a DASHI proposal |

## Generic semantic-intervention theorem

For input `x`, model `f`, latent encoder `h`, decoder `g`, and intervention `T`, the new generic contract separates:

```text
h(Tx) = tau_T(h(x))
g(tau_T(z)) = T_Y(g(z))
g(h(x)) = f(x)
```

from which the formal owners derive

```text
f(Tx) = T_Y(f(x)).
```

A second theorem composes intervention-equivariance witnesses when the input and output interventions themselves compose.

## Candidate geometries

The comparison surface keeps six candidates typed separately:

```text
unstructured baseline
LILA E8 root prior
Monster 3A local geometry
Monster 3B Heisenberg geometry
Monster 3C local geometry
generic finite action geometry
```

No candidate wins by name, cardinality, or aesthetic similarity. A comparison receipt is expected to use held-out paired perturbations and nuisance controls.

## T5 relative complement

Existing trialectic work gives

```text
T9 ~= T4 x T5
|T5| = 3^5 = 243.
```

The new candidate chooses the constant diagonal

```text
(t,t,t,t,t),  t in {-1,0,+1},
```

as a canonical three-state locus. Lean computes

```text
|diagonal T5|     = 3
|non-diagonal T5| = 240
243 = 3 + 240.
```

This is deliberately **not** the theorem `non-diagonal T5 = E8 roots`. Promotion requires an explicit equivalence from a concrete E8 root carrier to the relative T5 carrier and an action-intertwining law. Count equality alone cannot construct the recognition record.

## 3B composition and cocycle diagnostic

The existing Agda Heisenberg carrier has

```text
g = (a,b,c)
h = (A,B,C)
```

with composition phase containing

```text
c + C + b dot A.
```

The existing full Schrodinger action satisfies

```text
rho(g*h) f = rho(g) (rho(h) f).
```

The new semantic fitting socket therefore asks a proposed intervention `T` to carry an actual fitted group element `g_T` and tests both

```text
h(Tx) ~= rho(g_T) h(x)
```

and the stronger composition condition

```text
g_(T1 o T2) ~= g_T1 * g_T2.
```

The central/cocycle defect is separately traceable. This is stronger than nearest-root geometry or a raw output flip rate.

## Relative orientation

The source status around the recent 3B `t1/t2` work is preserved:

```text
t1 literal source word        paid
t2 central-subgroup role      paid
t2 exact matrix element       open
t2 scalar orientation         open
historical q-word alignment   open
```

This is used as a model-design lesson only: recovering two features/carriers is weaker than recovering their relative phase/orientation and composition law.

## Surface plus dependent residual

Geometric reasoning reuses the repository's mature information-loss discipline:

```text
state -> geometric surface + dependent residual -> exact reopen.
```

Consumers are classified as surface-only, selected-residual, or full-state. Residual availability does not itself prove residual necessity; a concrete collision must be owned by the relevant consumer.

## Experiment trace

The formal trace schema carries, per layer and intervention:

- paired semantic accuracy;
- displacement alignment;
- E8/root occupancy or entropy statistic;
- quantization error;
- fitted-action error;
- composition defect;
- central/cocycle defect;
- nuisance response;
- DASHI projected-delta admissibility.

The intended experiment compares baseline, E8 and Monster candidate geometries on the **same** semantic intervention pairs and nuisance controls.

## DASHI-proposed action-compression quality

The typed score surface corresponds to the qualitative form

```text
semantic information * composition fidelity
--------------------------------------------
action complexity + residual complexity
```

with the precise score algebra supplied by a concrete experiment. This is a proposed DASHI definition, not an attributed Sophontic metric and not an empirical result.
