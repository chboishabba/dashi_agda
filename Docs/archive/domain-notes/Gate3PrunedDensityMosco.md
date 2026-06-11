# Gate3 Pruned Density / Mosco Receipt

Canonical receipt:
`DASHI/Physics/Closure/Gate3PrunedDensityMoscoReceipt.agda`

## Closed Model Theorem

The p-adic frame-carrier side is treated as closed for the Gate3 support lane:

- `SSPFrameCarrierEqualsOKTensorZ3`
- `BTIdentityGramUniformFrame`
- `A_N(L2(Q_p)) = 1`

The finite pruned Archimedean model is also recorded:

- `55/120` atoms retained
- retention rate `0.458`
- finite lower bound `A_N >= 0.010`
- verified through `N <= 55`

## Failed Naive Transfer

The direct Archimedean frame transfer is marked false.

Reason:

- deep BT atoms collide in `R3`
- Gram rows become near-identical
- lower eigenvalue collapse appears around `N ~= 27`
- the power-weighted embedding route fails because the collision is angular,
  not radial

## Remaining Promotion Lemma

The exact Gate3 support blocker is now density/Mosco:

```text
PrunedSSPSpectralTransfer
  = finite pruned lower bound
  + level-density lower bound
  + continuum covering/separation control
  + PrunedFrameDenseInHContinuum
  + Mosco recovery
```

Finite pruning evidence alone does not imply continuum density.

All Gate3 and Clay promotion flags remain false.
