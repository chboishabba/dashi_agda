# NS Cumulative Tail Dominance Obstruction

This is the concrete Navier-Stokes worker receipt for isolating the remaining
Clay-facing inequality.

## Consumed In-Repo Support

```text
NSTailFluxLPIdentityFullDerivationReceipt:
  fixed K selected before differentiation
  pressure term cancels
  viscous term has the right sign
  moving-cutoff term is absent
  adjacent leakage and theta<1 remain open

NSDangerShellMaxPrincipleConditionalProofReceipt:
  conditional danger-shell implication is recorded
  circularity is identified
  H^{1/2} high-high control would be circular
  H^{-1/2} nonlinear defect replacement remains open
```

## Current Split

```text
HighHigh:
  recorded as absorptive partial result.

HighLow / LowHigh:
  live obstruction.
```

The named Clay-facing lemma is now:

```text
HighLowFluxControlWithoutRegularity:
  ||P_{>K}(u_{<K} * grad u_{>K})||_{H^{-1/2}}
    <= eps * nu * ||P_{>K}u||_{H^{3/2}}
  without assuming global ||u_{<K}||_{L^infty} control.
```

## Concrete Sublemmas

```text
1. FixedKTailFluxIdentity
2. ParaproductFluxDecomposition
3. HighHighFluxBoundPartial
4. HighLowFluxControlWithoutRegularity
5. LowHighFluxBound
6. TailDissipationLowerBound
7. FluxOverDissipationThetaLtOne
8. NoGlobalRegularityInput
```

## Obstruction Rule

Any proof of cumulative tail dominance that assumes Serrin, BKM, global
regularity, or the target `H^{11/8}` bound is rejected as circular.

The next concrete test is:

```text
Can high-low/low-high paraproduct flux be absorbed by tail dissipation above
K_nu without importing global regularity?
```

No Navier-Stokes or Clay promotion follows from this obstruction receipt.
