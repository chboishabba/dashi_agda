# Moonshine Proof Checklist

This checklist turns the moonshine-primes exploration into a staged proof
program with explicit stop conditions.

## Tier 1: Empirical non-accident

1. Formalize the observed object.
   Reference:
   [`MoonshinePrimeObject.md`](./MoonshinePrimeObject.md)
2. Define and run null models.
   Reference:
   [`MoonshinePrimeNullModels.md`](./MoonshinePrimeNullModels.md)
3. Promotion gate:
   if any null reproduces the prime-specific structure at the required
   threshold, stop the moonshine bridge program and downgrade the claim.

## Tier 2: Structural theorem

4. Identify the algebraic carrier/factorization surface.
   Reference:
   [`CarrierFactorization.md`](./CarrierFactorization.md)
5. State the canonical prime-selection law.
   Reference:
   [`CanonicalPrimeSelectionLaw.md`](./CanonicalPrimeSelectionLaw.md)
6. Promotion gate:
   no Monster/Ogg comparison is allowed until the construction selects primes by
   an intrinsic arithmetic property `P` of the quotient object, not by raw
   coincidence.

## Tier 3: Moonshine bridge

7. Record the bounded CRT/J scalar bridge.
   Reference:
   [`CoreSpineBridge.md`](./CoreSpineBridge.md),
   `DASHI.Algebra.MoonshineBridge`, and
   `DASHI.Physics.CRTPeriodJFixedBridge`.
   This proves only the local identity
   `CRTPeriod.period + 1 == JFixedPoint.contract JFixedPoint.unit-obs` and the
   p47/p59/p71 active-wall channel positions.
8. State the legal moonshine-match test forms.
   Reference:
   [`MoonshineMatch.md`](./MoonshineMatch.md)
9. State the promotion gate from primes to modular objects.
   Reference:
   [`PrimeToModular.md`](./PrimeToModular.md)
10. Promotion gate:
   no genuine moonshine claim is allowed without a modular curve, Hecke,
   Hauptmodul-like, or trace-level lift.

## Best next proof target

The next theorem target is not “prove moonshine”.

It is:

> the primes produced by the basin construction are selected by an intrinsic
> arithmetic property of the quotient object, not by incidental numerics.

That means the current execution order should be:

1. make the observed object executable,
2. make the null-model stop condition executable,
3. isolate one carrier/factorization hypothesis,
4. use the landed CRT/J scalar bridge only as a bounded structural bridge,
5. formulate and test the prime-selection property `P`.
