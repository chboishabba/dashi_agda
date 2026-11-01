# NS filament fining: formal core and runtime bridge

## Scope

This tranche formalises the signed-support filament-fining mechanism developed in the sibling `dashiCFD` Vulkan decoder without promoting a numerical codec into a Navier–Stokes theorem.

The implementation is split deliberately:

- `DASHI.Physics.Closure.NSFilamentFiningCore` is the finite theorem-bearing kernel.
- `DASHI.Physics.Closure.NSFilamentFiningRuntimeBridge` is the empirical/runtime receipt.
- `DASHI.Physics.Closure.NSFilamentFiningRegression` contains compile-time witnesses.

The bridge imports `DASHI.Physics.Closure.NSFastestClayPathReceipt`, so the existing current NS route and its fail-closed Clay boundary remain authoritative. The signed carrier is the existing `Base369.TriTruth` spine: `tri-low` is zero/annihilated support and `tri-mid`, `tri-high` are the two signed support states.

## Formal transition

For a cell with signed support `s`, lifetime `n`, and a coherence decision `c`:

```text
survive(s,c) = support(s) AND c

fine(c,(s,n)) =
  (s,n+1)       when survive(s,c)
  (0,0)         otherwise
```

The proved finite laws are:

1. failed coherence annihilates every sign state;
2. coherent positive and negative support preserve sign and increment lifetime;
3. annihilated support is absorbing;
4. lifetime-shaped acceptance may protect existing support but cannot resurrect annihilated support.

This gives the precise version of the working sentence:

> Filament fining is the irreversible projection of signed support whose coherence fails to persist; surviving support increments a persistent local lifetime, while annihilated support is absorbing.

## Tracking choice

Per-cell lifetime is canonical for the state transition because annihilation mutates support locally. Per-block and per-mode lifetimes remain useful derived summaries, but they are not interchangeable with the local state:

- **per-cell**: exact local fining state; canonical;
- **per-block**: compact spatial summary; may blur thin filaments;
- **per-mode**: spectral persistence summary; does not localise support.

## Minimal metrics contract

The theorem-bearing minimal metrics shape is:

```text
alive : Nat
killed : Nat
maxLifetime : Nat
```

Distributional metrics such as mean, p90, p99, and alive fraction are intentionally left as an open runtime gate. They should be added as derived observables rather than altering the local transition definition.

## Runtime receipt

The runtime bridge records the tested sibling `dashiCFD` facts:

- explicit vkFFT inverse-normalisation invariant;
- Vulkan decode actually selected;
- CPU/Vulkan decoded-field parity at printed precision;
- CPU/Vulkan low-pass parity at printed precision;
- exact printed mask match;
- persistent per-cell lifetime buffer;
- compact alive/killed/max-lifetime metrics;
- lifetime-shaped annihilation acceptance using the currently recorded `0.85` relaxation factor;
- parity-only mode without GT plots.

The canonical observed parity command is recorded in the Agda receipt. The reported snapshot surface had decoded-field relative L2 `0.0000`, correlation `1.0000`, low-pass relative L2 `0.0000`, and mask match `1.000` at printed precision for `t = 300..3000`.

This is a candidate runtime receipt, not a universal bitwise theorem across devices, resolutions, drivers, or future kernels.

## Important experiment correction

The three commands labelled `baseline`, `lifetime`, and `lifetime_strict` differed only in output filenames. They did **not** pass different lifetime-policy parameters. Therefore their identical GT traces establish neither a lifetime effect nor a null effect.

A real three-way experiment remains open and must expose explicit policy parameters, for example:

```text
baseline: relaxation factor = 1.0 or shaping disabled
shaped:   relaxation factor = 0.85, canonical min-life
strict:   relaxation factor = 0.85, larger min-life
```

The next honest runtime work is therefore:

1. parameterise shaping enable/factor/min-life;
2. emit lifetime distribution metrics;
3. run the actual controlled sweep with identical seeds and artifacts;
4. compare codec fidelity, support churn, and lifetime distributions;
5. keep CPU/Vulkan parity as a mandatory implementation gate.

## Non-promotion boundary

This tranche does not prove:

- that the local coherence proxy identifies physical vortex filaments;
- that lifetime shaping improves reconstruction;
- that codec error bounds LES or Navier–Stokes error;
- no coherence replenishment at high shells;
- non-Beltrami coherent tubes cannot persist;
- BKM/Serrin continuation;
- Navier–Stokes regularity or Clay promotion.

Those remain governed by the existing NS closure receipts, especially `NSFastestClayPathReceipt` and the current fail-closed route ledger.
