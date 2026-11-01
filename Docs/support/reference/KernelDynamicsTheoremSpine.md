# Kernel dynamics theorem spine

This tranche moves the DASHI kernel work from terminology and bridge notes into a typed dynamics spine.  It remains fail-closed: generic convergence is not promoted unless a concrete carrier supplies the required collision or descent witness.

## Added formal surfaces

- `DASHI.Core.KernelSystem`
  - typed state, site, channel, geometry, neighbourhood, and weight-family carriers;
  - canonical synchronous kernel;
  - explicit scheduled implementations;
  - involution and kernel/involution equivariance;
  - proof-bearing equivalence relation and quotient-respecting kernel.

- `DASHI.Core.KernelOrbit`
  - forward iteration;
  - fixed points;
  - positive-period orbits;
  - one-step quotient stability;
  - all-phase quotient collapse;
  - eventual-periodicity witnesses.

- `DASHI.Core.KernelRenormalization`
  - strict commutation;
  - commutation after quotient;
  - bounded-defect commutation;
  - strict commutation implies quotient commutation.

- `DASHI.MDL.KernelStrictDescent`
  - strict MDL descent outside literal fixed points;
  - strict MDL descent outside quotient-stable classes;
  - bounded fixed-point and quotient-stabilisation certificates.

- `DASHI.Core.FiniteKernelDynamics`
  - explicit orbit-collision certificates;
  - conversion of collisions to eventual periodicity;
  - a finite deterministic kernel interface whose eventual-periodicity theorem is proof-bearing rather than asserted from a Boolean finiteness flag.

- `DASHI.Trading.PermissionKernel`
  - typed market-window state;
  - quotient invariants for shape, energy, persistence, liquidity, and risk;
  - `ACT / HOLD / BAN` permission classification;
  - quotient-respecting and schedule-explicit kernel instance;
  - one-step idempotence and fixed-point stabilisation;
  - all-phase quotient collapse;
  - non-increasing action receipt;
  - learner output restricted to quotient readout rather than an execution command.

## Claims now discharged

For the concrete trading permission kernel:

```text
permissionKernel (permissionKernel s) = permissionKernel s
```

so every market state reaches a literal permission fixed point after one canonical update.  The kernel preserves the market quotient on every step, hence every orbit lies in one quotient class.  Its declared action is unchanged by permission normalisation, giving a non-increase receipt without claiming strict descent.

## Remaining proof gates

1. Run the repository Agda compiler and repair any library-version or universe mismatch.
2. Prove a reusable pigeonhole theorem deriving `every-orbit-collides` from a finite enumeration and decidable equality, rather than carrying it as a field.
3. Add a well-founded natural-valued descent theorem deriving `ReachesFixedPointWithin` or `ReachesQuotientStableWithin` from strict MDL descent.
4. Replace the trading placeholder geometry/neighbourhood/weight carriers with the concrete rolling-window and channel-coupling implementation once that runtime contract is fixed.
5. Add empirical receipts connecting observed market windows to the typed quotient features; these remain data claims, not consequences of the abstract kernel definitions.

## Non-promotion boundary

This tranche does not prove convergence of arbitrary threshold kernels, does not make the diagnostic inconsistency count `E(s)` a Lyapunov function, does not equate DASHI eigen-objects with cortical modes, and does not allow the learner to issue broker execution commands.
