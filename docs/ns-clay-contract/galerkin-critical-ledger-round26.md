# Round 26 — finite Galerkin cancellation and duplicate-free critical taxes

[Back to the Clay-contract overview](README.md)

Round 25 proved that every literal cutoff resonant interaction belongs to exactly one physical support class. Round 26 applies the same fail-closed discipline to the next layer: finite Galerkin algebra, physical signed-shell assembly and analytic tax ownership.

This round does **not** prove global regularity. It does not instantiate continuum Picard–Lindelöf, produce the time-dependent physical shell balance, prove a cutoff-uniform nonlinear estimate, or prove the strict viscosity margin.

## Exact advances

### Literal degree-two Galerkin coordinate algebra

`NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact.agda` represents every finite coordinate equation as a list of linear viscous atoms and bilinear resonant-triad atoms. Every atom has degree at most two by construction.

For each bilinear atom the exact identity

```text
xy - uv = (x-u)y + u(y-v)
```

is proved and lifted to finite sums. This is the algebraic input to a local-Lipschitz estimate on a normed real coordinate space; it is not itself the continuum-real ODE theorem.

### Reality reconstruction rather than an independent constraint

`NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact.agda` stores one coefficient for each selected positive reality orbit and reconstructs

```text
mode(-)  = -mode(+),
value(-) = conjugate(value(+)).
```

Reality is therefore structural. Negative-mode transversality follows from an explicit `ConjugateTransversalityLaw`; that law still needs a concrete continuum-real instance.

### Physical and scalar triadwise energy cancellation

The repository already contained the stronger physical theorem in `NSTriadKNComplex3EnergyCancellation.agda`: for the actual signed Leray coefficient, exact reality condition and divergence-free condition, every physical resonant triad has a complete three-leg cancellation certificate.

`NSTriadKNLuoTriadwiseEnergyCancellationRound26Exact.agda` now re-exports that theorem at the Round 26 boundary and adds a transparent rational six-term audit normal form.

For `p+q+k=0`, transversality yields

```text
a·k = -a·q,
b·k = -b·p,
c·p = -c·q.
```

The two ordered placements at each of the three outputs then satisfy

```text
T_k + T_p + T_q = 0.
```

A finite list of complete scalar normal forms consequently has zero internal transfer. Nonzero cumulative shell flux must arise from cutting physical triads across shell or Galerkin boundaries.

### Signed critical shell ledger

`NSTriadKNLuoSignedCriticalLedgerRound26Exact.agda` keeps the identity signed. Each shell has separate coordinates for

```text
HH, LH, HL, CC, Com, lower boundary, upper boundary.
```

After multiplication by an arbitrary critical weight, finite summation preserves the exact equality. Positive parts are introduced only later, after available cancellation has been used.

The same module proves the division-free weight identity

```text
weight · vorticityEnergy
= criticalVelocityWeight · velocityEnergy
```

from

```text
vorticityEnergy = frequencySquared · velocityEnergy,
weight · frequencySquared = criticalVelocityWeight.
```

The homogeneous critical carrier excludes the zero mode; arbitrary periodic means are restored only at the final Galilean step.

### Physical five-source signed-shell bridge

`NSTriadKNLuoPhysicalSignedShellCellRound26Exact.agda` prevents the signed shell ledger from being populated by unrelated scalars.

It starts from the literal Round 25 evaluator

```text
fiveSourceTotal = HH + LH + HL + CC + Com(output)
```

and accepts one genuine shell balance

```text
energyRate + dissipation
= fiveSourceTotal + lowerBoundary + upperBoundary.
```

The resulting `SignedCriticalShellCell` has its five source coordinates forced by the actual physical output fibre. The caller cannot choose `HH`, `LH`, `HL`, `CC` or `Com` independently.

This closes the source-coordinate bridge. It does **not** yet derive the time-dependent shell balance from a constructed Galerkin trajectory; that remains the live L3/L5 analytic producer.

### Low transport and finite commutator

`NSTriadKNLuoLowTransportCommutatorRound26Exact.agda` fixes naming by derivative placement. For a divergence-free low velocity advecting the tested high vorticity, the principal self-tested transport term cancels exactly.

It also connects directly to the existing periodic far-low stack:

- `NSPeriodicFarLowExactCommutatorIdentity.agda` proves the tested projected shell identity;
- `NSPeriodicFarLowMultiplierDifferenceKernel.agda` retains the signed multiplier-difference kernel separately from its absolute majorant;
- `NSPeriodicFarLowMultiplierDifferenceBound.agda` proves the pointwise mean-value reduction while leaving the cutoff-uniform operator estimate conditional.

`NSTriadKNLuoFiniteKernelCommutatorRound26Exact.agda` additionally proves cellwise and for finite sums

```text
w a(x-y) ∇b(x-y) - a(x) w ∇b(x-y)
= w (a(x-y)-a(x)) ∇b(x-y).
```

It also proves exact first-moment scaling under literal displacement rescaling. The continuum estimate

```text
||[P_q,a·∇]b||_2
≤ C 2^{-q} ||∇a||_∞ ||∇b||_2
```

and the stronger signed/spectral alternative remain open quantitative producers.

### Division-free high–high defect normalization

`NSTriadKNLuoDivisionFreeHHDefectRound26Exact.agda` avoids defining a quotient by a potentially vanishing denominator. It stores

```text
A = d² Z,
Z M = D²,
```

and proves

```text
A M = d² D².
```

The zero branch is explicit:

```text
Z = 0 ⇒ A = 0.
```

The ordered real/square-root step needed to derive a one-sided continuum inequality remains open.

### Hysteretic entry charge

`NSTriadKNLuoHystereticPositiveVariationRound26Exact.agda` replaces unsupported excursion counting by a finite positive-variation theorem. Every entry satisfying

```text
before + h ≤ after
```

pays at least `h` from its positive rise. Therefore

```text
sum(entry gaps) ≤ sum(positive rises).
```

The physical PDE estimate controlling total positive variation across all scales remains open.

### Duplicate-free tax ownership

`NSTriadKNLuoDuplicateFreeTaxOwnershipRound26Exact.agda` assigns each taxable atom exactly one owner:

```text
HH-good, HH-bad, LH, HL, CC, Com, kernel, tail, boundary.
```

Erasing ownership reconstructs the original total exactly. This prevents the same kernel, tail, commutator, or excursion term from consuming viscosity twice.

`NSTriadKNLuoCriticalRemainderClassificationRound26Exact.agda` similarly requires every remainder to be one of:

```text
data-controlled, time-integrable, small, telescoping.
```

It records the only generic Grönwall-admissible shape as

```text
R = A_T + B · integratedCriticalEnergy.
```

### Finite adversarial regressions

The Agda and Python regressions reject two false proof moves:

```text
1 + (-1) = 0,
but taxing both magnitudes costs 2;
```

and

```text
one nonzero atom assigned to two owners is counted twice.
```

The Python script also exhaustively checks the finite commutator identity and six-term triad cancellation on a configurable integer box.

## Exact remaining boundary

Round 26 has not proved:

1. a concrete continuum-real `ConjugateTransversalityLaw`;
2. Picard–Lindelöf for the literal real finite phase space;
3. global finite Galerkin existence from the physical energy identity;
4. the physical time-dependent filtered-vorticity shell balance and its boundary atoms;
5. any cutoff-independent classwise tax;
6. the periodic principal-value strain kernel and Calderón–Zygmund estimates;
7. the PDE positive-variation budget;
8. the strict total coefficient `η_total < 1`;
9. shell or Galerkin limit passage;
10. unconditional periodic Navier–Stokes regularity.

## Highest-alpha next step

The next tranche should complete the concrete finite ODE and then prove one actual quantitative tax. The preferred analytic target is the low-advection commutator package:

```text
principal transport cancellation
+ exact projected shell identity
+ signed multiplier-difference kernel
+ pointwise mean-value reduction
+ cutoff-uniform signed/operator estimate
+ critical shell summation
⇒ cutoff-independent Com/low-advection tax.
```

Progress is measured by an inhabited cutoff-independent estimate or a finite counterexample that invalidates it, not by additional interface count.
