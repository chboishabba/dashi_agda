# Yang--Mills Agda/Lean Clay assembly cross-prover handoff — 2026-09-16

Status: current cross-prover bookkeeping. This document records theorem interfaces and certification boundaries; it is not theorem authority and does not claim an unconditional Clay solution.

## Active lanes

Agda current-master source integration:

- PR #987, branch `agent/ym-final-direct-upper-closure`;
- merged #970 / R387 least-privilege source ABI:

```text
|D^2_{J_L,J_R} log Z_N| <= selected clusteringEnvelope(O,t).
```

Lean operator/assembly integration:

- dashi_lean4 PR #7, branch `agent/ym-vacuum-gap-backward-bounds`;
- opt-in retained libraries `YMFinal`, `YMBidi`, and now `YMClay`;
- active consumer `Welds.YMClayAssembly`.

## Retained Clay assembly

The supplied Aristotle task `ym-clay-assembly-task-3eea48e0-20260916` contributes:

```text
RequestProject.YangMills.Clay.FormHamiltonian
RequestProject.YangMills.Clay.BoundedCoreEvolution
RequestProject.YangMills.Clay.MassGapAssembly
RequestProject.YangMills.Clay.AssemblyWitness
RequestProject.YangMills.Clay.LatticeDefectInstance
```

The supplied worker receipt reports `lake build RequestProject` green end-to-end (8207 jobs), with no `sorry`, `axiom`, `postulate`, or `@[implemented_by]` in the new material and headline axiom audits limited to `propext`, `Classical.choice`, and `Quot.sound`.

That receipt belongs to the supplied Aristotle source. Current branch integration must obtain its own exact-head receipt before being called kernel-certified.

## Bounded-form compression

`FormHamiltonian` proves, for a bounded Hermitian sesquilinear form `q_a` on a complex Hilbert space,

```text
<z,H_a y> = q_a(z,y)
q_a Hermitian -> H_a self-adjoint
q_a(-,Omega_a)=0 -> H_a Omega_a=0
Delta-coercivity on Omega_a^perp -> VacuumGapDatum(H_a,Omega_a,Delta)
```

Thus in the bounded finite-spacing route operator existence, self-adjointness, the zero-vacuum equation, and the finite gap datum are no longer separate proof-search leaves.

`BoundedCoreEvolution` additionally proves that a bounded everywhere-defined Hamiltonian is closed as a partial-domain operator, has the whole Hilbert space as a core, and generates `t |-> exp(tH)`. Hence bounded core/generator hypotheses are compiler output; only the actual physical same-object YM/OS evolution equality remains external to that compiler.

## Active source-to-Clay theorem

Lean #7 now exposes:

```text
Welds.YMClayAssembly.massGapOfSourceCovariance
```

Its visible inputs are exactly:

```text
Delta > 0
CutoffFamily C
forall cutoff n:
  SpectralRepresentation (C.ham n) (C.vacuum n)
  continuum/source covariance carrier covInf_n
  OS/Laplace comparison
  source covariance decay at rate Delta
OSWeld C.limitHam H_OS
```

The theorem composes:

```text
ClusteringSpectralData.ofSourceBound
-> hasVacuumFormGap_of_clustering
-> uniform finite HasVacuumFormGap
-> Clay.clay_mass_gap_of_inputs
-> vacuum graph-limit transport
-> same-evolution OS weld
-> MassGapConclusion H_OS Omega Delta.
```

Therefore once the Agda R387 direct upper is attached to the same physical cutoff covariance/spectral carrier, there is no further generic theorem gap between that decay statement and the final Lean mass-gap conclusion.

## Active energy-form theorem

Lean #7 also exposes:

```text
Welds.YMClayAssembly.massGapOfEnergyForms
```

with theorem shape

```text
EnergyFormFamily Delta
+ CutoffFamily
+ exact Hamiltonian-family identity
+ exact vacuum-family identity
+ OSWeld
-----------------------------------
MassGapConclusion H_OS Omega Delta.
```

The retained `Clay.clay_mass_gap_rowA1` specializes this route to the existing positive Row-A1 constant `bMinus (casimirAdjointSU N) r h` under the already-formalized small-remainder conditions.

## Final cross-prover normal form

The formal assembly is now:

```text
SOURCE/HYBRID:
  Agda/CMP116 direct selected covariance upper on the physical cutoff family
  + per-cutoff physical SpectralRepresentation

OR

ENERGY-FORM:
  literal physical bounded Hermitian q_a
  + q_a(-,Omega_a)=0
  + uniform Delta-coercivity

THEN COMMON:
  physical CutoffFamily vacuum graph limit
  + physical OSWeld / YM=OS same-object evolution

=> Lean MassGapConclusion H_OS Omega Delta.
```

`MassGapConclusion` includes the vacuum form gap, no eigenvalue in `(0,Delta)`, unique vacuum-sector solvability of `H psi - lambda psi = y` for every real `lambda < Delta`, and the `(Delta-lambda)^-1` resolvent bound.

## What is no longer a live generic leaf

Do not reopen without a consumer forcing it:

- R410 as mandatory terminal architecture;
- another source calculus or covariance carrier;
- another clustering-to-gap theorem;
- separate bounded finite-Hamiltonian existence/self-adjointness/vacuum/core/generator proofs;
- another finite-to-continuum gap compiler;
- another same-evolution gap-transfer compiler;
- another terminal resolvent/eigenvalue theorem.

## Remaining physical inhabitants

The remaining debt is entirely in the visible physical theorem inputs, not in generic assembly:

```text
1. selected CMP116/source decay attached to the same physical cutoff covariance carrier,
   or a literal physical coercive EnergyFormFamily;
2. the actual physical cutoff-to-continuum vacuum graph limit / continuum Hamiltonian data;
3. the actual YM/OS same-object evolution/reconstruction weld.
```

These may not be replaced by `ProofLevel`, Boolean status, citations, postulates, synthetic witnesses, or record fields with unproved payloads.

## Certification boundary

At Lean #7 integration head `7bf7580859eb6f15259fe595cc9c37e3789dc40f`, GitHub reports CodeRabbit success but no PR-triggered Lean workflow run. Therefore the active cross-lane weld is source-written pending exact-head kernel verification. The supplied Aristotle Clay tranche retains its own 8207-job worker receipt only.
