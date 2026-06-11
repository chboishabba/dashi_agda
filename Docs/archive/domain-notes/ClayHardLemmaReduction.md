# Clay Hard-Lemma Reduction

This note records the corrected way to use the analytic sprint toward the
Clay-facing lanes.  The sprint does not promote a solution.  It converts
metaphor-heavy pressure into exact proof targets with named failure modes.

## Yang-Mills

The old shortcut is closed:

```text
T7 grows slower than j
  -> C0_eff ~= 2
  -> beta_eff > 15.84 is enough
```

The corrected pipeline is:

```text
raw j-growth
  -> T7A coefficient audit
  -> connected-animal KP count
       sum_d d * p^(d-1) * exp(-beta*c_min*d) < 1
  -> non-perturbative RG bridge
  -> OS positivity + infinite volume + Wightman
  -> Clay YM promotion
```

The direct T7A KP sum is proved, but it is not the best counting route:

```text
KPThreshold_connectedAnimal = 9.59
GapFromPhysical             = 3.59
KPThreshold_T7A_direct      = 16.56
T7A_is_best_counting_route  = false
C0_eff_justified            = false
```

The earlier surrogate regimes remain useful only as diagnostics:

```text
raw Monster j envelope -> beta* ~= 64.9
T7 Rademacher envelope -> beta* ~= 32.6
C0 = 2 heuristic      -> beta* ~= 15.9
direct T7A KP sum     -> beta* ~= 16.56
connected animal      -> beta* ~= 9.59
```

This buys one concrete improvement for Clay: the entropy-side YM target is no
longer a debated constant.  The standard computable route is connected-animal
counting at `beta* ~= 9.59`, while T7A can improve the route only if it is
proved as per-polymer activity suppression rather than count replacement.
Yang-Mills still needs the non-perturbative Balaban scale transfer from
physical `beta ~= 6` to the active KP margin, then the OS/Wightman continuum
package.  Keep the margin conventions separate: connected-animal `9.59`,
p=7 BT-tree `10.11`, and safe KP margin `13.64`.

## Gate3 / Frame

The Monster/T7/zeta7 material is useful for the frame lane only as a
phase-completeness reduction.  It explains why a phase-blind atom dictionary
loses the inert/complex character information and why MirrorB7 is not
decorative.

The hard Gate3 frame targets remain:

```text
A_split > 0
A_inert > 0
A_71 > 0
uniform cutoff lower bound
Mosco / no-spectral-pollution lift
```

The latest toy-model attempt sharpens the failure mode: a 1D Gram model with
phase sectors orthogonal by position makes phase-blind and phase-complete
dictionaries identical.  Phase can only affect the cross-Gram when different
phase sectors overlap spatially, which is a property of the full 3D
Archimedean image.

Phase completeness is therefore necessary only in the physical 3D model, not
something a 1D toy can prove.  It sharpens the frame proof target; it does not
close Gate3.

## Gravity / SSP 3D Embedding

The useful gravity result is the exact 3D taper threshold:

```text
sigma_crit,3D(p=3) = 0.3025113508228815
sigma_digit        = 0.2886751345948129
headroom           ~= 0.0138
```

The digit baseline passes.  The open theorem is the physical transfer:

```text
PhysicalSSPEmbeddingSpreadLemma:
  prove sigma_physical_SSP < 0.3025113508228815
```

This is a Hecke/Archimedean embedding estimate.  It does not provide W4 mass
calibration or a Schwarzschild weak-field match.

## Navier-Stokes

The representation-theoretic material has no direct Clay-NS force.

Path A is an obstruction paper:

```text
H^{-1/2} defect ratio diverges like a negative power of nu.
```

Path B is the Clay-facing route:

```text
H^{11/8} Bernoulli-band global bound
K* drift control without global regularity input
carrier-structured-to-all-smooth-data extension
```

All Navier-Stokes promotion flags remain false.

## Promotion Boundary

The practical solve strategy is now four proof campaigns:

1. Use connected-animal KP counting as the YM entropy target and prove the
   Balaban bridge from `beta ~= 6` to the active KP margin (`9.59`, `10.11`,
   or safe `13.64`); separately prove or refute T7A per-polymer activity
   suppression as an improvement route.
2. Prove Gate3 phase-complete frame lower bounds in the physical 3D image.
3. Prove the physical SSP/Hecke 3D spread inequality.
4. Publish the NS obstruction and separately attack the non-circular
   `H^{11/8}` / `K*` route.

The ledger remains fail-closed: no Clay, Gate3, gravity, Schwarzschild, W4,
Balaban, OS/Wightman, NS, or terminal promotion follows from this reduction.
