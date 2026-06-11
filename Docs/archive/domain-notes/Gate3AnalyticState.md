# Gate3 Analytic State

Status: analytic bridge narrowed, not closed. No Gate3 or Clay promotion.

## Proof Tree

1. Finite cutoff frame lower bound
   - Receipt: `Gate3FiniteCutoffFrameLowerBoundProofReceipt`
   - Result: at a selected finite cutoff `H_N`, a positive lower frame bound `A_N > 0` is recorded as finite evidence.
   - Boundary: this is not a cutoff-independent lower bound on the infinite continuum Hilbert space.

2. Uniform lower-bound obstruction
   - Receipt: `Gate3UniformLowerBoundObstructionReceipt`
   - Result: `inf_N A_N > 0` is exactly the missing uniform/separation problem.
   - Boundary: finite `A_N > 0` does not imply a continuum frame bound.

3. Constructive Mosco recovery sequence
   - Receipt: `Gate3MoscoConstructiveSequenceReceipt`
   - Result: finite dual-frame projections give the canonical recovery candidates.
   - Boundary: Mosco condition I is equivalent to density plus PAWOTG transfer; both remain open.

4. Conditional no spectral pollution
   - Receipt: `Gate3NoSpectralPollutionConditionalProofReceipt`
   - Result: the Attouch/Mosco route is recorded conditionally: Mosco form convergence can feed strong resolvent convergence, but no spectral pollution still needs compactness/tightness, isolated-sector, and spectral-projection hypotheses.
   - Boundary: unconditional no-spectral-pollution is not proved.

## Diagnostic

Script: `../dashiCFD/scripts/gate3_frame_extended_sweep.py`

Output: `../dashiCFD/gate3_frame_extended.csv`

The sweep computes empirical Gram eigenvalue bounds for phase-complete and phase-blind synthetic dictionaries at `N = 8, 16, 32, 64, 128`. The observed minimum `A_N` is very small (`~9.7e-08` in the default run), so the empirical surface supports the fail-closed reading: phase completeness alone is not enough unless the PAWOTG separation/net condition is made precise.

Refined sampler-quality output:

```text
Docs/Images/clay-analytic-sprint/gate3_sampler_quality.csv
```

The current sampler has zero Gershgorin-passing rows.  Its `mu_N` values are
near `1`, while the strict row-sum target is `mu_N < 1/(N-1)`.  The next
engineering target is therefore not another sweep of the same sampler but:

```text
AtomSamplerPAWOTGQuality : mu_N <= C / N
```

or at least enough spacing to make `(N-1)mu_N < 1` for the Gershgorin route.

## Single Blocking Condition

The current Gate3 blocker is:

```text
PAWOTG_1_over_N_net_condition
```

It must prove density plus enough uniform separation/tightness to keep the cutoff frame bounds from collapsing and to prevent spectral pollution in the limit.

The narrowed concrete condition is the BT overlap series:

```text
S_p(sigma) = sum_{d>=1} p^d exp(-((log p)^2 d^2)/(4 sigma^2)) < 1
```

The current computed inert-prime threshold table is:

| Prime/block | `sigma_crit` |
| --- | --- |
| `p=3` | `0.5052` binding |
| `p=5` | `0.6225` |
| `p=13` | `0.7891` |
| `p=17` | `0.8334` |
| `p=19-59` | `0.86-1.05` |

Monster re-2 / second-irrep entropy stress tightens this condition if raw
representation multiplicity leaks into the overlap count.  The relevant
artifact is:

```text
Docs/Images/clay-analytic-sprint/gate3_monster_re2_sigma_crit.csv
```

At the binding inert prime `p=3`:

```text
C0 = 1 baseline                  -> sigma_crit = 0.505208
C0 = log(c2/c1) ~= 4.69          -> sigma_crit = 0.337460
C0 = sqrt(irrep2/irrep1) ~= 10.40 -> sigma_crit = 0.296102
C0 = sqrt(c2/c1) ~= 10.45        -> sigma_crit = 0.295905
C0 = irrep2/irrep1 ~= 108.17     -> sigma_crit = 0.228435
C0 = c2/c1 ~= 109.17             -> sigma_crit = 0.228254
```

So the Gate3 lane now has the same upstream quotient obligation as YM:
`MonsterMultiplicityQuotientControl`.  Baseline `sigma < 0.5052` is the
correct target only after the carrier quotient prevents raw Monster
multiplicity from entering PAWOTG overlap entropy.

The proposed attack route is Weil-representation/theta-symbol computation of
the Archimedean spread after adelic transfer.  The `p=2` Kozyrev/Haar proved
case is relevant evidence with `sigma=0`, but it does not close SSP `p>=3`
localization or the Gate3 PAWOTG blocker.

## Publication Posture

Publishable claim: Gate3 has been reduced to a finite-frame plus Mosco/no-pollution bridge with a named PAWOTG blocker.

Forbidden claim: carrier control has been transferred to continuum Sobolev or mass-shell control.
