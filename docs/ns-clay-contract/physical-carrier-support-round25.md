# Round 25 — literal Galerkin carrier and physical five-class support

[Back to the Clay-contract overview](README.md)

Round 25 follows the highest-alpha order identified in Round 24: inspect the existing repository before inventing a new carrier, close the exact finite support problem, and leave analytic estimates fail-closed.

## Existing content reused

The repository already contained:

- the literal periodic cutoff cube and complete resonant triad enumeration;
- soundness, completeness and duplicate-freeness of that enumeration;
- exact output-indexed resonant fibres;
- reality closure under `k ↦ -k`;
- the exact Leray-projected Fourier coefficient;
- coefficientwise equivalence between the projected physical equation and the finite Galerkin ODE;
- the executable four-way scale classifier;
- exact dyadic shell consequences for low–high, high–low and high–high-to-low interactions.

Round 25 composes these facts instead of duplicating them.

## New L3 carrier theorem

`NSTriadKNLuoLiteralGalerkinCarrierRound25Exact.agda` proves that filtering the duplicate-free resonant enumeration by one output mode preserves duplicate-freeness. Therefore every physical output fibre is:

- resonance-sound;
- cutoff-sound;
- complete;
- duplicate-free.

For every finite cutoff `N`, the module constructs one `LiteralGalerkinCarrierCertificate N` containing the complete finite combinatorial carrier and the literal reality policy. It also connects the physical projected coefficient to the exact output-indexed Galerkin coefficient.

The aggregate L3 node remains open only at the following analytic instance:

```text
finite-dimensional ODE existence over the selected continuum real carrier;
propagation of reality and transversality along that ODE.
```

The Fourier enumeration, output fibres, Leray coefficient and physical/Fourier coefficient identity are no longer open L3 subclauses.

## New shell no-go theorem

Let `jp,jq,jk` denote the exact ceiling-log dyadic shell indices of a resonant triad `p+q=k`, with the repository separation constant `Csep=3`.

Round 25 proves:

```text
jp + 3 ≤ jk
and
jq + 3 ≤ jk
imply contradiction.
```

Indeed, if `jp≤jq`, the exact max-norm triangle inequality gives

```text
jk ≤ jq+1,
```

contradicting `jq+3≤jk`; the other ordering is symmetric. Thus two inputs that are both three shells below an output cannot generate that output. This is the exact low-low-to-far-high exclusion required by the physical Bony partition.

## L4 physical support closure

`NSTriadKNLuoPhysicalFiveClassSupportRound25Exact.agda` classifies every literal physical resonant triad uniquely as one of:

```text
LH, HL, HH, CC.
```

The classes carry quantitative consequences:

```text
LH: |jk-jq| ≤ 1,
HL: |jk-jp| ≤ 1,
HH: |jp-jq| ≤ 1.
```

The differentiated commutator is retained as the fifth class `Com`. There is no residual or catch-all constructor. Classification of every output fibre erases exactly to the original physical fibre, and the appended commutator cell computes to class `Com`.

`NSTriadKNLuoPhysicalFiveClassSumRound25Exact.agda` evaluates the actual five-source fibre using:

```text
triadValue : PhysicalTriad → ℚ,
commutator : FourierMode → ℚ.
```

A triadic cell is evaluated by `triadValue` on its stored incidence. The `differentiatedCommutator k` cell is evaluated by the same mode-indexed functional at its stored output, namely `commutator k`. Folding this evaluator over `fiveSourceOutputFiber N k` proves

```text
Fphysical
=
FHH + FLH + FHL + FCC,
```

and

```text
Ftotal(N,k)
=
FHH + FLH + FHL + FCC + commutator(k).
```

Thus the fifth value is derived from the appended `Com` cell and its output mode; it is not inserted as an unrelated scalar. These are exact finite equalities, not analytic estimates.

## Ladder change

Round 25 changes the ladder exactly once:

```text
L4 exhaustive physical Bony/commutator support:
physicalProducerOpen → checkedExact.
```

L3 remains open in narrowed form. L7 remains the next nonlinear producer:

```text
Fi(q,Q,N;t)
≤ ηi DQ,N(t) + Ai(t) + Bi XQ,N(t),
```

with every coefficient uniform in `q,Q,N,T*`.

No classwise analytic coefficient, strict viscosity margin, cutoff limit, smooth global solution or Clay theorem is claimed in this round.

## Source metadata

The Agda headers record:

- Jean Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, DOI `10.1007/BF02547354`;
- Roger Temam, *Navier-Stokes Equations: Theory and Numerical Analysis*, DOI `10.1090/chel/343`;
- Jean-Michel Bony, *Calcul symbolique et propagation des singularites pour les equations aux derivees partielles non lineaires*, DOI `10.24033/asens.1404`;
- Hajer Bahouri, Jean-Yves Chemin and Raphael Danchin, *Fourier Analysis and Nonlinear Partial Differential Equations*, DOI `10.1007/978-3-642-16830-7`;
- Xiaoyutao Luo, *A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization*, DOI `10.1007/s00021-019-0411-z`.

## Validation command

```bash
AGDA_JOBS=1 bash scripts/check_ns_luo_physical_carrier_support_round25.sh
```

An absent kernel result leaves the new formal tranche unpromoted operationally even though the intended theorem status is represented fail-closed in source.
