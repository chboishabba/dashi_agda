# Round 34 — physical selected-background radius and W-local assembly

Parent index: [Yang–Mills Reference Index](./YangMillsReferenceIndex.md)

Previous round: [Round 33 paper audit and all-group guards](./YangMillsPaperAuditRound33.md)

Literal Clay contract: [Round 32 contract and gate invariants](./YangMillsClayContractRound32.md)

## Purpose

Round 34 advances the first unresolved physical cut identified after Round 33. It does not add another terminal receipt. It proves the quaternion and ordered-rational mathematics needed to derive the physical link radius from Bałaban's selected background, then gives the exact constructor that turns correlated physical plaquette bounds into the repository's actual W-local hypothesis.

The dependency chain is now:

```text
Bałaban variational fine-bond estimate
  -> literal inverse-link norm-square radius
  -> positive scalar hemisphere
  -> selected principal logarithm and inverse orientation
  -> correlated linear + grouped nonlinear plaquette control
  -> physical W-local
  -> 10739/196608 > 1/32 terminal Hessian floor
```

The remaining open producer is the physical correlated plaquette estimate itself, not radius bookkeeping or a generic signed-order adapter.

## Formal owners

- [Physical relaxed radius to principal chart](../../Physics/YangMills/BalabanP33RelaxedRadiusPrincipalChartExact.agda)
- [Selected background physical-radius instantiation](../../Physics/YangMills/BalabanSelectedBackgroundPhysicalRadiusInstantiationExact.agda)
- [Physical linear/remainder W-local constructor](../../Physics/YangMills/BalabanP33PhysicalLinearRemainderWLocalExact.agda)
- [Round 34 cumulative validation root](../../Physics/YangMills/BalabanClayHighestAlphaRound34PhysicalRadiusWLocalValidation.agda)

## Exact quaternion theorem

For a literal rational unit quaternion `U`, Round 34 proves

```text
N(U^-1 - 1) = 2 (1 - q0(U)).
```

The configured P33 gauge estimate uses

```text
rho = 1/8192,
N(U^-1 - 1) <= 4 rho^2.
```

Cancellation of the positive factor `2` yields

```text
1 - q0(U) <= 2 rho^2,
```

therefore

```text
1 - 2 rho^2 <= q0(U).
```

The exact rational constant `1 - 2 rho^2` is strictly positive. Consequently every selected physical link satisfying the relaxed radius lies in the positive-scalar hemisphere and is separated from the antipodal logarithm cut.

The standard Hall principal-chart theorem is still represented explicitly: the physical theorem supplies positive scalar part, while the chart recognition field supplies the standard implication from positive scalar part to membership in the selected principal image. These roles are not conflated.

## Variational theorem to physical radius

The physical instantiation fixes the generic Round-33 bridge to:

```text
FineField = literal RationalSU2Background4
Bond      = literal side-four positive bond
Group     = rational unit quaternion
Bound     = exact rational
```

The source theorem and repository carrier are joined by the following exact identifications:

```text
source order relation = rational order
selected source bond value = physical link
selected source defect = N(U^-1 - 1)
published fine-bond upper <= 4 rho^2
physical conjugation = selected chart inverse
```

The code then derives, rather than assumes,

```text
RelaxedInverseLinkRadius selectedBackground.
```

For the same selected background it also proves:

```text
physical link belongs to the selected principal image
log(U^-1) = -log(U).
```

The perturbation family requires every Hessian perturbation to use that exact selected background. The existing terminal theorem therefore no longer receives a free-standing radius witness: its radius is generated from the variational source estimate.

## Physical W-local constructor

For each literal plaquette `p`, the actual Wilson defect is decomposed as

```text
D2W_A(p)[h,h] - D2W_1(p)[h,h]
  = linearPart(p) + groupedRemainder(p).
```

Round 34 requires the exact signed estimates

```text
-(rho/36) C_p(h) <= linearPart(p),
-(rho/144) q_p(h) <= groupedRemainder(p).
```

Here `C_p` is the repository's twelve-pair cross charge and `q_p` is its four-slot diagonal charge. Their sum is definitionally the existing local Wilson budget. The module constructs

```text
PhysicalWilsonSignedLocal A h
```

directly from these two physical inequalities.

No independent scalar defect, anonymous budget or citation receipt is accepted by the constructor.

## Terminal theorem after Round 34

For one selected background and one physical perturbation object, the following inputs now suffice:

1. the physically instantiated Bałaban variational/chart bridge;
2. componentwise mean zero;
3. exact constraint residual background;
4. the per-plaquette correlated linear/remainder control.

The cumulative theorem then derives

```text
H_A[h,h] >= 10739/196608 ||h||^2
           > 1/32 ||h||^2.
```

The radius premise and W-local record are no longer independent caller-supplied objects.

## Exact remaining Gate-I mathematics

The next queue is deliberately narrow:

```text
selectedBackgroundPlaquetteFirstVariation
selectedBackgroundCovariantDiscreteCurlIdentity
selectedBackgroundCurvatureLower
physicalWilsonLinearPartIdentification
groupedSixteenAtomNonlinearRemainderLower
```

The target inequalities are exactly

```text
-(rho/36) C_p(h) <= linearPart(p),
-(rho/144) q_p(h) <= groupedRemainder(p).
```

Once those are proved for every physical plaquette, Round 34 already composes them through W-local to the terminal Hessian floor.

## Subsequent gates

After Gate I closes, the highest-alpha order remains:

```text
literal Hessian matrix and exact stencil
  -> row/column interaction mass
  -> constructive inverse
  -> physical Combes–Thomas decay
  -> differentiated physical Schur complement
  -> uniform fluctuation coercivity and inverse decay
  -> strict RG loss 32 E_k < 2 - theta_k
  -> all-scale RG induction
  -> interacting measure
  -> changing-spacing continuum OS theory
  -> local curvature operators, AF, stress tensor and OPE
  -> no-spectral-pollution Hamiltonian gap
  -> every compact simple group
```

## Sources

The Agda headers record:

- Kenneth G. Wilson, *Confinement of Quarks*, DOI `10.1103/PhysRevD.10.2445`;
- Tadeusz Bałaban, *The Variational Problem and Background Fields in Renormalization Group Method for Lattice Gauge Theories*, DOI `10.1007/BF01229381`;
- Tadeusz Bałaban, *Propagators for Lattice Gauge Theories in a Background Field*, DOI `10.1007/BF01240355`;
- Brian C. Hall, *Lie Groups, Lie Algebras, and Representations*, DOI `10.1007/978-3-319-13467-3`.

## Verification boundary

Focused command:

```bash
AGDA_JOBS=1 bash scripts/check_yang_mills_clay_highest_alpha_round34.sh
```

The checker cascades through Round 33, rejects holes, postulates, unsafe escapes, trust primitives and imported theorem receipts, verifies the new theorem/source/documentation guards, and invokes the pinned Agda 2.9 cumulative root.

A static audit is not a kernel result. The branch remains draft until the dedicated workflow has produced an observed successful Agda status.
