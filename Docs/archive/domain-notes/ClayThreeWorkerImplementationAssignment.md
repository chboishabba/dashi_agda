# Clay Three-Worker Implementation Assignment

Historical note: this was the first worker split for the lane.  The live
Sprint 3 worker split is now
`Docs/ClaySprintThreeSixWorkerAssignment.md`.

This receipt assigns one implementation worker to each shortest live bridge.

## W1 Gate3

```text
Worker: W1-Gate3
Task: implement or kill SSPCarrierEqualsHeckeModel
Source receipt: PhysicalSSPHeckeModelClosureReceipt
```

Success routes:

```text
SSPCarrierEqualsHeckeModel
  -> HeckeModelSpreadBound
  -> S3DAtHeckeSpreadBelowOne
  -> UniformFrameLowerBound
```

Failure leaves Gate3 support blocked at carrier/model identification.

## W2 Navier-Stokes

```text
Worker: W2-NS
Task: implement HighLowFluxControl audit or counterfamily
Source receipt: NSHighLowFluxControlAuditReceipt
```

Allowed route:

```text
prove K^(-1/2) HighLow suppression
without hidden L_infinity / Serrin / BKM / global H^(11/8)
```

Failure route:

```text
produce Leray-energy-bounded HighLow counterfamily
```

## W3 Yang-Mills

```text
Worker: W3-YM
Task: implement 42-step Balaban target
Source receipt: YMFortyTwoStepBalabanTargetReceipt
```

Target:

```text
FortyTwoStepBalabanUniformity
FortyTwoStepLeakageSummable
FortyTwoStepStrictSeedReach toward beta_eff >= 13.7
```

Failure must return the exact failed block-spin step or failed leakage bound.

## Boundary

This is an ownership receipt, not a theorem receipt.  No Clay, Gate3, YM, NS,
W4, gravity, Schwarzschild, or terminal promotion follows from worker
assignment.
