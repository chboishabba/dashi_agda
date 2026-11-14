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

## 2026-10-24 selected graph discriminator for 243=3+240

Cross-branch consumer: [KK/Casimir #1241](https://github.com/chboishabba/dashi_agda/pull/1241), source `scripts/check_kk_240_243_e8_portal_casimir_bidi.py`. This does NOT claim #1241 is merged into this branch.

Our source-owned `T5E8RelativeComplementCandidateExact.agda` already makes the 3^5=243 → three diagonal +240 remaining states exact, while correctly withholding E8 recognition/action intertwining. The downstream executable tests a specific *natural* graph embedding question. The non-diagonal 240 states of P3^5 have induced degree distribution `5:40,6:70,7:80,8:50`; the C3^5 periodic version has `9:30,10:210`; classical E8 root inner-product-1 adjacency is **56-regular** on 240 roots. Therefore NO graph isomorphism exists from either of these selected ternary edge operators to that E8 root graph. It is not a universal impossibility of alternative 240-state equivariant recognition and does not refute the original purely arithmetic construction.

The *same numeral* 240 also appears as the ideal-plate Casimir pressure denominator and ~240 in a QED+QCD one-loop stationary-radion defect; different physical quantities/units/operators. Neither is an E8-root action witness. Attribution stays with original classical E8/Casimir results, this source's arithmetic carrier, and selected downstream computation respectively. Agda kernel of this downstream module remains unverified.

## Conditional E6 trinification 48-vector Casimir donor

External representation-theory SOURCE ROOT: R. Slansky, *Group theory for unified model building*, *Physics Reports* 79 (1981), 1–128, DOI 10.1016/0370-1573(81)90092-2, tables 53 (E8) and 58 (E6). These original branching rules give E8 adjoint 248 → (78,1)+(1,8)+(27,3)+(27bar,3bar), and E6 adjoint 78 → three SU3 adjoints (8+8+8) plus two 27-dimensional mixed representations. This is genuine representation prior art, not inferred from the 243−3=240 ternary carrier.

DOWNSTREAM conditional physical consumer [KK #1241](https://github.com/chboishabba/dashi_agda/pull/1241): selecting SU3_colour and two extra SU3 factors gives 16 further 5D gauge vectors, 16×3=48 bosonic Casimir polarizations, exactly the free massless-limit compensation for (6 flavours×3 colours×4 Dirac)−(8 gluons×3 pols)=48 fermionic excess. At the chosen b0 and nonzero physical quark masses, a toy all-degenerate additional vector mass ≈86.31 GeV is needed. The compensator is NOT a phenomenologically accepted trinification action; symmetry breaking, vector couplings, collider constraints, chiral fermions, Higgs portal, QCD running and the 5D source stress remain open.

The ternary 240-site graph has NO graph isomorphism to the classical E8 root inner-product-one graph, so the group-theoretic SU3 branching does not repair the missing root-operator intertwiner in this original branch. Preserve all three distinct source roles.

## E6 Casimir physically stronger correction: Wilson/Higgsed vectors

The later physically sourced [KK #1241](https://github.com/chboishabba/dashi_agda/pull/1241) test **supersedes** any interpretation of the early 86.31GeV scalar-like tuning mass as a real vector mass. Ordinary 5D massless Yang–Mills fields have 3 polarizations, but 5D Higgsed massive vectors have 4 and require the full Higgs/ghost spectrum.

With the *true massless* extra SU3³ gauge factors, a slight neutral bulk mass retuning restores the RADION stationary equation, but the physical electric charges of six quarks make U_EM-Wilson-theta-theta≈−21.189, not a stable vacuum. This is a consumer-indexed failure of the selected trinification-motivated free KK candidate, not of the original E8 or 243 arithmetic. It does not grant an E8 root intertwiner or a physically completed group unification.