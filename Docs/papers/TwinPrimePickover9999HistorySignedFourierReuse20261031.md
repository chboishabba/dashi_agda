# Retained 9999 phase-history ↔ twin-prime signed Fourier fibre reuse (31 Oct 2026)

## Source-level audit

Inspected **PR #1260** `chatgpt/eisenstein9-crt-pickover-rh-maxcut-20261025`:
- `DASHI.Analysis.PickoverConsumerResidualFibreBridgeExact`: imports the original `ConsumerIndexedResidualRefinementExact`; `residualNeededForSignedCollision` proves any consumer-sufficient repair separates a collision on which the sign differs. `signedFibreStrictlyRefinesSector` provides a strict refinement theorem. The 99^(9999!) analytic phase instance remains explicitly open.
- `DASHI.Analysis.PickoverAnalyticJHistoricalPhaseConsumerExact`: `RetainedBishopPhaseHistory` stores prior/live/terminal complex phases; `analyticJHistorySineExact` recovers genuine Bishop sine only after `ActualAnalyticTerminalPhase.terminalIsTrueTrig` supplies the true-phase equality. This **does not** decide the sine sign.
- Original `DASHI.Core.ConsumerIndexedResidualRefinementExact`: sufficient observers must distinguish every collision relevant to their selected consumer, with exact residual repair and strict refinement.

Inspected current **PR #1408**:
- `DASHI.Arithmetic.TwinPrimeFractranResidualHyperfabricExact`: directly imports the above residual repair and Pickover bridge; includes SSP valuation witnesses distinguishing genuine 59 from composite 329. Finite recorded examples are not a density theorem.
- `DASHI.Arithmetic.TwinPrimeResidualMangoldtBidiExact`: `liftNatConsumer`, `liftConsumerSound`, `liftConsumerComplete`, and `periodResidualUniqueness` use the *unbounded* period index plus `Fin270`. Arbitrary actual Nat consumers, including Mangoldt and shifted pair correlation, retain exact values; this is stronger than reducing n mod 270.
- `DASHI.Arithmetic.TwinPrimeResidualMangoldtPeriodRowsExact`: row-by-row finite-sum BIDI without discarding rejected residue positions.
- `DASHI.Physics.WaveAlgorithmLift`: cancellation must be supplied in `InterferencePruningBridge`; historical/projection fibres do not imply cancellation on their own.

## Reuse now committed

`DASHI/Arithmetic/TwinPrimeSignedFourierHistoryConsumerBidiExact.agda` defines a *consumer-specific* signed-shell readout and reuses `TwinPrimeResidualMangoldtBidiExact.liftConsumerSound` and `liftConsumerComplete` to prove both directions through the existing retained period fibre. It does **not** duplicate the fibre, import branch-only PR #1260 into PR #1408, or assert a distribution theorem.

## The exact next discriminator

For a signed shell contribution `T_j(X)` to the arithmetic Fourier representation of actual shifted Mangoldt sums, preserve the pair `(coarse projection, history/residual)` along each refinement, and prove an identity `sum_j T_j(X)=S(X)` including every cross-shell term (if the filters overlap). Only **after** this, seek bounds

`S(X)= main(X)+sum_j T_j^error(X)` with `main(X) ~ 2*C2*X`
and `sum_j T_j^error(X)=o(X)`.

An exact fibre makes the lossless transport square commute; it cannot by itself supply the final signed cancellation estimate. This is analogous to the Pickover distinction between terminal history equals actual sine phase and a certified sign-separating enclosure. In both cases the remaining obligation is **analytic quantitative control of the original consumer**, not a further finite observer encoding.

Respect source ownership: original core fibre owners, Pickover PR #1260, signed SSP/FRACTRAN arithmetic authors, Hardy–Littlewood, and finite Fourier/LP mathematical predecessors. No ESD edits. Source-written ≠ Agda kernel-verified.
