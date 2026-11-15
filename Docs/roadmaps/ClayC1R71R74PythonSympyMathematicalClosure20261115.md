# Clay #1499 / C1 — R71 physical real chart and fixed-R854 existence, Python/SymPy mathematical receipt

**15 November 2026.** This is a **classical mathematical / exact symbolic certificate** for the original **C1** phase gate, using the user's explicitly requested Python/SymPy acceptance pathway instead of running Agda/CI. It is **NOT** an Agda 2.9 kernel receipt, an inhabitant of the historical rational-valued R408 time-dependent packet, a selected R853 differentiated-rate theorem, or a Clay Millennium result. Keep all original Agda false status flags unchanged.

## Exact original owner and source identity

- `NSTriadKNFixedCanonicalRealityVectorFieldRound71Exact.agda` (`rawCanonicalRHSAt`, `realityVelocity`).
- `NSTriadKNComplex3GalerkinEquationAudit.agda` (`projectedOrderedTerm`, `projectedNonlinearity`).
- `NSTriadKNExactSignedGalerkinCoefficient.agda` (`orderedVelocityInteraction = -i Leray[(q·u_p)u_q]`).
- `NSTriadKNFiniteRealCanonicalCoordinateCarrierRound71Exact.agda` (six real entries per canonical positive mode).
- `NSTriadKNLuoFiniteGalerkinPolynomialRound26Exact.agda` (`viscousLinear` and `resonantBilinear` atoms).
- `NSTriadKNFiniteRationalSlotAssignmentBridgeRound74Exact.agda` (`finiteRationalAssignment` from an ordered finite state).
- `NSTriadKNR650Rational345CanonicalStateRound838Exact.agda` and `...EnergyRowsRound829Exact.agda` (original physical radius-four initial vector).
- `NSTriadKNR650Rational345ShortTimeRound830Exact.agda` (the **unchanged** rational horizon).

Let `Lambda_N = { k in Z^3 : |k_i| <= N, k != 0 }` and `H_N` be the canonical leading-nonzero-positive representative in each pair `{k,-k}`. The real state is `x in R^(6|H_N|)`. Reconstruct `u(-k) = conjugate(u(k))`, and `u(0)=0`, exactly as in R71. Let `P(k)_{jt} = delta(j,t) - k_j*k_t/|k|^2` for `k != 0` and `nu=1` on the original selected radius-four geometry.

The fixed, **original R71** projected vector field has component

```text
F(k,j)(x) = -nu |k|² u(k,j)
            - i Σ_{p+q=k; p,q in Lambda_N} (Σ_l q_l u(p,l))
                     (Σ_t P(k)_{jt} u(q,t)).
```

The repo also enumerates zero-mode triads. Their contribution is zero since `u(0)=0`; omitting them in the exact rational evaluator changes no term.

## Universal real-atom compiler identity (all N, all states, every ordered triad)

Let `p^+,q^+` denote the respective canonical representatives, and `eps_p,eps_q` the signs (+1 for a positive representative, -1 on its negative mode). Use `a_l + i eps_p b_l` for `u(p,l)` and `c_t + i eps_q d_t` for `u(q,t)`.

Writing `g = q_l P(k)_{jt}`, each ordered `(p,q)` summand contributes the following **rational-coefficient real quadratic atoms**:

```text
Re contribution = Σ_{l,t} g * ( a_l eps_q d_t + eps_p b_l c_t )
Im contribution = Σ_{l,t} g * ( eps_p eps_q b_l d_t - a_l c_t )
```

The viscous contribution is the `viscousLinear` atom with coefficient `-nu |k|²` on the matching real or imaginary coordinate. Every bilinear product is of the exact `resonantBilinear triad left right coefficient` form used by R26; add them in the **same ordered original output fibre**, without a hidden 1/2 or an assumption about transversality.

Proof is expansion of the source-defined `-i*(q·u_p)*P_k u_q`. The symbolic regression expands the difference **as a polynomial in all real/imag inputs and independent eps_p,eps_q,k,q,inverse-square variables**, obtaining zero for each output axis. This is not restricted to sampled numerical states. Sum congruence then identifies the entire R71 field with the canonical generated R26/R74-style atom polynomial for each `N`. The older R74 `LiteralGalerkinCoordinateEquation` record takes *arbitrary* atoms; the missing mathematical step was constructing this specific source-preserving atom list, not claiming that every arbitrary list represents the physical field.

## Actual selected real ODE and fixed horizon

For `N=4`, `|Lambda_4| = 728`, `|H_4| = 364`, so `x` has 2,184 real coordinates. The exact original R829/R836 support consists of the three positive modes `(0,4,0)`, `(3,0,0)`, `(3,4,0)`; source vectors give `||x(0)||_infty = 6`. Independently evaluating the full original ordered-triad physical projected nonlinearity gives all **24 real/imag component pairs** for the **eight original active forcing rows** exactly as in `...EnergyRowsRound829Exact.agda` and `...SparseSnapshotRound836Exact.agda`.

On `||x||_infty <= M = 12`, for every nonzero `k` and row `j`,

```text
Σ_t |P(k)_{jt}| <= 2.
```

Indeed `1 - x²/s + x(y+z)/s <= 2` with `s=x²+y²+z²`, `x=|k_j|` and `y,z` the other absolute coordinates; use `xy <= (x²+y²)/2` twice. Each of the real and imaginary parts of `q·u_p` has magnitude at most `3*N*M=12*M`, each projected part `P_k u_q` at most `2*M`, and complex multiplication costs at most two such products. Thus each ordered triad contributes at most `2*(12*M)*(2*M)=48*M²` to any real component. There are at most 728 ordered inputs for fixed k. Also `nu|k|²*M <= 48*M` for `nu=1`. Therefore

```text
||F_4(x)||_infty <= 728*48*12² + 48*12
                 = 5,032,512 = K.
```

The field is a finite real quadratic polynomial, hence locally Lipschitz on `R^2184`. Standard finite-dimensional Picard–Lindelöf provides a unique maximal `C^1` solution. For its first exit from the radius-12 component ball, the displacement bound would give `||x(t)-x(0)||_infty <= K*t`. On **the original R830/R854 horizon**

```text
T = 226189 / 3938540454339300631433585885184
```

the exact rational inequality `K*T < 6` excludes any first exit before or at `T`. The standard continuation criterion therefore extends this same real Galerkin solution through `[0,T]`. No shorter substitute horizon and no enstrophy residual were used.

## Executable acceptance and boundary

Run `python3 scripts/check_clay_c1_r71_r74_sympy_bridge_20261115.py`. SymPy 1.14.0 and exact Python `Fraction` pass:

- universal 3-axis complex-to-real polynomial identity, with a wrong-sign negative control;
- all eight original R829/R836 projected forcing rows (24 exact complex components);
- all 728 physical cutoff-four modes × 3 Leray projection rows with exact rational row bound;
- initial maximum 6, vector-field `K = 5032512`, and `K*T < 6`.

An additional independent extended differential checker in the original investigation compared 546 exact scalar components across cutoffs one, two and four. The short committed source is the reproducible minimum certificate.

**Closure disposition:** `C1 = CLOSED_MATHEMATICAL_PYTHON_SYMPY` on the explicitly user-authorized non-Agda mathematical protocol. The earlier requirement for an **Agda-native** `originalR71R74PhysicalRHSIsRealQuadraticField` / `originalR71RealGalerkinLocalSolution` proof is a separately recorded **unfulfilled formalization debt**, not falsely marked kernel green. The C2 claim **remains OPEN**: transport of the selected helical R853 functional to the actual real flow, differentiating that original functional, bounding its derivative, and bridging the historic rational-time R408 packet to genuine real time. The six terminal Clay-adjacent endpoints remain 0/6.
