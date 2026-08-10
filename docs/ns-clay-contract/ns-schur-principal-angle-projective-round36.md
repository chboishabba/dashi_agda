# NS Round 36 — Schur inverse scale, principal-angle falsification, and projective owner ledgers

Round 36 starts from the repaired Round-35 fixed-cutoff carrier and attacks the concrete mechanism proposals rather than adding another terminal closure wrapper.

## HH-bad: Schur/Feshbach scaling is now falsifiable

For a fine parabolic block with scale

```text
D ~ nu lambda^2,
D^-1 ~ nu^-1 lambda^-2,
```

the exact signed scale ledger proves:

```text
(one derivative) * D^-1 * (bounded coupling)
  ~ nu^-1 lambda^-1,

(bounded coupling) * D^-1 * (one derivative)
  ~ nu^-1 lambda^-1,

(one derivative) * D^-1 * (one derivative)
  ~ nu^-1 lambda^0.
```

So the Schur route can manufacture the uniquely required inverse shell power only when exactly one off-diagonal coupling spends one derivative. If both sides spend a derivative, the inverse shell gain is cancelled and the result is scale-free. The physical task is therefore sharply typed: identify the literal HH-bad block decomposition and prove that its derivative bookkeeping is of the one-derivative form. The branch does not assert such a block realization exists.

## HH-bad: a dissipative bad-stratum floor would also produce the inverse scale

A second exact mechanism is implemented. If entering the bad stratum at shell `q` has floor

```text
Gamma_q = nu lambda_q
```

and occupation is chargeable by

```text
occupation_q * Gamma_q <= dissipationCharge_q,
```

then exact dyadic reciprocal algebra gives

```text
occupation_q * nu
  <= dissipationCharge_q * lambda_q^-1.
```

Thus the zero-point/residual-floor idea is not merely interpretive: a genuine lower dissipative price for bad membership would produce precisely one inverse shell power. The still-open physical theorem is the implication from the actual Luo/HH-bad stratum to this floor.

## HH-good: mode principal angles alone are refuted

Round 35 showed that `sqrt(2) S_k` is isometric on each transverse vorticity fibre. Round 36 tests whether separation of the wave-vector directions alone can make the cross-fibre Gram small.

The exact witness is

```text
k = e1,
l = e2,
omega = eta = e3.
```

Then `k dot l = 0`, `e3` is transverse to both modes, and each normalized same-fibre Gram is one, yet

```text
2 <S_e1 e3, S_e2 e3>_F = -1.
```

Hence orthogonal mode directions can still have unit-magnitude normalized strain-fibre correlation. A bound depending only on the angle between `k` and `l` cannot be the missing HH-good smallness theorem. The surviving high-alpha route must use additional physical structure: periodic principal-value cancellation, increments, vorticity-direction coherence, spatial localization, shell localization, or a combination of these.

## Com: exact coarse/fine naturality defect

The commutator interpretation is made literal on a finite exact kernel carrier. For

```text
P f = sum_y K_y f_y,
T_y f_y = u_y f_y,
```

Round 36 proves

```text
P(T f) - u_x P f
  = sum_y K_y (u_y - u_x) f_y.
```

So `Com` is exactly the defect of the coarse/fine transport square, and the defect vanishes when velocity is constant on the coarse fibre. The remaining A1 theorem is still operator-valued: realize the actual `T_q^* T_r` and `T_q T_r^*` through the Round-35 Gram cells and the centered increment structure.

## Finite shell budgets form a coherent projective ledger

Round 35 proved `I_Q + B_Q = eta` and `B_(Q+1) = (1/2) B_Q`. Round 36 proves the finite semigroup law

```text
2^-(m+n) = 2^-m 2^-n
```

and therefore

```text
B_(Q+n) = B_Q 2^-n.
```

All finite cutoff shadows carry exactly the same total owner resource. This is the correct projective finite ledger for the later shell-cutoff limit. The analytic theorem that the physical boundary term vanishes and that the physical owner inequality survives `Q -> infinity` remains separate.

## Nine-owner robustness is a region, not a point

A robust owner budget is represented by an exact inner box of coefficient envelopes `u_i` satisfying

```text
eta_i <= u_i,
sum_i u_i < 1.
```

The branch proves automatically

```text
sum_i eta_i <= sum_i u_i < 1.
```

and specializes the construction to the repository's literal `NineOwnerEstimateFamily`. Thus a future physical proof can certify a region of admissible allocations rather than one brittle tuned point. The physical upper envelopes are not fabricated here.

## Triad selection rules are a proof-bearing hypergraph

A retained triad is now an actual hyperedge carrying membership in the existing `ExactRetainedSectorLaw`. Every edge therefore has exact zero momentum. The Round-35 `S3 x C2(reality)` action is lifted to hyperedges, and all twelve factored actions preserve retention and momentum closure while allowing stabilizers.

Nonzero interaction strength is deliberately represented by a separate `PhysicalCouplingSelectionLaw`: momentum closure and cutoff membership do not imply nonzero coupling.

## F2: the complete-real coordinate seam is now typed correctly

The old Round-30 coordinate interface uses rational assignments. That is the right exact syntax for rational Galerkin coefficients, but it is not the complete trajectory carrier required by Picard--Lindelof. Round 34 already interpreted the same polynomial syntax on Murray--Bishop constructive reals, whose equality is a setoid relation rather than Agda propositional equality.

`NSTriadKNBishopSetoidCoordinateGluingRound36Exact` therefore defines the correct Bishop-real setoid coordinate equivalence. It requires genuine encode/decode round trips in the physical-state setoid and pointwise Bishop equality, plus coordinate reflection back to state equality. For any literal Galerkin representation it proves both faces of the vector-field square:

```text
encode(F_phys state) ~= F_coord(encode state),

F_phys(decode coordinates)
  ~=State decode(F_coord coordinates).
```

This removes the rational/completeness type mismatch without quotienting constructive-real equality by an unsafe axiom. The actual Fourier-state/Bishop-assignment codec and real Picard--Lindelof authority remain physical/analytic producers.

## Exact frontier after this round

The most informative new decision is negative: the simplest mode-principal-angle HH-good route is eliminated. The two live HH-bad inverse-scale mechanisms are now explicit and mutually checkable: one-derivative Schur elimination or a dissipative bad-stratum floor. `Com` is reduced to the literal operator realization of an exact increment/naturality defect. The finite shell and owner-budget limits now have coherent algebraic carriers, and the finite-flow lane now has a type-correct Bishop-real setoid seam rather than a rational surrogate.

None of these results is promoted to unconditional Navier–Stokes regularity. The physical PDE producers, actual Bishop-state coordinate codec, real Picard--Lindelof instance, nine actual owner estimates, cutoff limits, compactness and continuation remain required.
