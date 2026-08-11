# Round 29 — dependent physical flow and falsifiable owner analysis

[Back to the Clay-contract overview](README.md)

Round 29 follows the highest-alpha route identified after Round 28. It advances the actual finite-flow and owner-estimate boundary without claiming a physical cutoff-uniform Navier–Stokes estimate.

## Exact mathematics

### Reconstructed physical state space

The finite state stores only positive reality-orbit coefficients with transversality evidence and a dependent zero-mode exclusion. Negative coefficients are reconstructed by complex conjugation. Their transversality and nonzero-mode status are proved.

Every positive and reconstructed-negative coefficient is also proved fixed by the literal `Complex3` Leray projector. Because reality, transversality and centering are intrinsic to the state type, the concrete selector on this state space is the identity triple. The open theorem is that the full viscous-plus-quadratic Galerkin vector field maps the reconstructed state type to itself.

### Dependent physical ODE carrier

For any vector field commuting with a commuting physical selector, the vector field lifts to

```text
PhysicalCarrier -> PhysicalCarrier.
```

Every derivative value therefore carries Leray, reality and centering evidence by construction.

### Complete finite-vector local Lipschitz estimate

Round 28 proved the estimate for one rational Galerkin coordinate. Round 29 sums the actual finite coordinate list and proves

```text
sum_alpha |F_alpha(u)-F_alpha(v)|
  <= (sum_alpha L_alpha(R)) delta
```

whenever every selected input coordinate lies in the radius-`R` ball and every coordinate difference is at most `delta`. The left side is the literal finite output `l1` norm, and the constant is the exact sum of the linear and bilinear atom weights.

The remaining finite-ODE bridge is the equivalence between this rational coordinate carrier and the selected continuum-real physical coordinate space, followed by the real Picard–Lindelöf instance.

### Finite continuation split

The finite flow argument is separated into:

```text
local flow;
finite-time blowup alternative;
energy control of the finite norm.
```

A uniform norm bound contradicts every escape witness. An energy bound constructs the required norm bound. Picard–Lindelöf and the literal physical energy identity remain open instances.

### One global pairing, five physical sources

One static output-fibre bilinear pairing is the authority. The exact Round-25 theorem derives

```text
Pairing = HH + LH + HL + CC + Com.
```

A dynamic shell balance may add only its chain-rule diffusion and named lower/upper boundary terms. It cannot independently change source signs or multiplicities.

### Delayed positive taxation

For every finite signed owner fibre,

```text
abs(sum constituents) <= sum(abs constituent).
```

The grouped positive part is likewise bounded by the atomwise positive-part sum under explicit subadditivity laws. The right side is named the lossy fallback; physical estimates should target the grouped left side.

### Signed commutator analysis

The sibling finite commutator coefficient theorem is integrated:

```text
2^-q * 2^q = 1.
```

A multiplier endpoint difference is proved equal to the exact signed telescoping sum along any finite path. Cross-shell signed cells aggregate under a local decay-mass certificate. This is the scalar core preceding an operator-valued Cotlar–Stein or `TT*` estimate; the cutoff-uniform operator theorem remains open.

### Scale-normalised bad amplitude

The raw cubic shell model is multiplied by one inverse shell scale, giving exactly the quadratic diffusion homogeneity:

```text
lambda^-1 * lambda^3 E = lambda^2 E.
```

This proves the required scaling correction, not a physical amplitude estimate or small coefficient.

### Falsifiable `HH-bad` criterion

The bad high–high lane records variation, amplitude and crossing costs. A parameter tuple is feasible only when their sum lies strictly below its allocation. If an unavoidable lower floor is already at least that allocation, the current estimate family is formally refuted.

### Symbolic owner optimisation

Every owner may retain an affine symbolic viscosity coefficient

```text
eta(epsilon) = etaBase + etaSlope * epsilon.
```

Only after all owners are assembled is a strict rational certificate selected. The symbolic certificate transports exactly into the existing admissible-owner budget.

### Boundary mechanisms

Boundary atoms are internally classified by the reason they vanish:

```text
exact absence;
fixed-cutoff finite support;
geometric tail;
strong convergence;
dominated convergence.
```

Their five subledgers reconstruct the signed boundary total exactly.

### Compactness and continuation reducers

The Galerkin time derivative is explicitly split into viscous and nonlinear negative-norm budgets. The quantitative critical-to-Serrin conclusion is

```text
||u||_(L4_t L6_x)^4
  <= C_S^4
     ||u||_(L-infinity_t H^(1/2)_x)^2
     ||u||_(L2_t H^(3/2)_x)^2.
```

The exponent identity `2/4 + 3/6 = 1` is checked exactly. The physical negative-norm bound, Aubin–Lions–Simon compactness and periodic Serrin continuation remain open.

## Exact remaining frontier

```text
1. prove literal nonlinear coefficient conjugation and vector-field invariance;
2. identify the rational finite vector with the continuum-real physical coordinates and instantiate Picard–Lindelöf;
3. derive the physical energy identity and global finite flow;
4. derive the time-dependent physical shell balance and boundary atoms;
5. prove the operator-valued cross-shell almost-orthogonality theorem;
6. construct the periodic principal-value strain kernel and CZ bounds;
7. produce physical good/bad HH, lower, kernel, tail and boundary estimates;
8. find a feasible symbolic nine-owner allocation with eta_total < 1;
9. pass the shell/Galerkin limits and instantiate Serrin continuation;
10. recover smooth periodic pressure, restore arbitrary mean and inhabit the literal Fefferman target.
```

## Scope boundary

Round 29 does not prove:

- the full nonlinear Galerkin vector field preserves the reconstructed carrier;
- continuum-real coordinate equivalence, Picard–Lindelöf or a global finite physical trajectory;
- the physical time-dependent shell equation;
- an operator-valued cutoff-uniform commutator estimate;
- the periodic singular-kernel theorem;
- any physical owner estimate;
- a physical strict viscosity margin;
- continuum compactness or continuation;
- unconditional periodic Navier–Stokes regularity.
