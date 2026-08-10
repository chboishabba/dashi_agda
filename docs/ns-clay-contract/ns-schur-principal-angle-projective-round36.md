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

Round 35 showed that `sqrt(2) S_k` is isometric on each transverse vorticity fibre. Round 36 first tests separation of wave-vector directions with the exact orthogonal witness

```text
k = e1,
l = e2,
omega = eta = e3.
```

Here `k dot l = 0`, `e3` is transverse to both modes, and each normalized same-fibre Gram is one, yet

```text
2 <S_e1 e3, S_e2 e3>_F = -1.
```

The stronger `NSTriadKNStrainFibreCoherenceBarrierRound36Exact` then treats every rational planar unit pair

```text
k = e1,
l = (c,s,0),
c^2+s^2 = 1.
```

Using the adapted transverse bases `e2,e3` and `(-s,c,0),e3`, the normalized cross-fibre Gram matrix is diagonal with channels

```text
c,
c^2-s^2,
```

and the mixed entries are exactly zero. Their squared channel energy satisfies the completion-of-squares identity

```text
c^2 + (c^2-s^2)^2
  = 7/16 + (2(c^2-3/8))^2
  >= 7/16.
```

So this is stronger than one counterexample: even with adapted polarizations, the two-channel cross-fibre coherence has a uniform positive floor. A mode-angle-only principal-angle argument cannot make the whole strain interference arbitrarily small. The surviving high-alpha route must use additional physical structure: periodic principal-value cancellation, increments, vorticity-direction coherence, spatial localization, shell localization, or a combination of these.

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

and specializes the construction to the repository's literal `NineOwnerEstimateFamily`. The abstract feasible-region layer also distinguishes the three outcomes suggested by the continuation analysis: `robustlyPositive` when a uniform strict envelope lies below one, `critical` when a feasible point has total exactly one, and `infeasible` when no point satisfies the producer constraints. This is the proof-theoretic version of optimizing the residual viscosity reserve without pretending an infimum or numerical optimizer has already been constructed.

## Triad selection rules are a cutoff-complete proof-bearing hypergraph

A retained triad edge now carries the repository's full `RetainedTriadMember`, not merely a sector Boolean. This includes exact-shell membership for the left, right, and output modes, exact zero momentum, and retained-sector membership. Consequently a zero-sum triad outside the fixed cutoff cannot be admitted.

Round 35's `S3 x C2(reality)` action is lifted to those full members. Cycle and swap transport the three shell witnesses by permutation. Round 36 additionally proves `inExactShellNeg`, so Fourier reality transports shell membership as well as the sector predicate. `RetainedHypergraphActionClosure` is inhabited closure evidence for all twelve factored actions; there is no direct `Bool=true` theorem receipt.

The follow-on `FullPhysicalTriadSelectionLaw` packages the full five-part active-transition test: exact momentum closure, exact cutoff/retained membership, transversality, Fourier-reality compatibility, and nonzero physical coupling. The last three remain genuine physical predicates, but their permutation/reality covariance is explicit. `FullFivePartSelectionClosure` proves that all twelve factored actions preserve the complete package. Thus F4/HH-bad can later count or weight genuinely active transition orbits rather than every nominal shell pair.

## F2: the complete-real coordinate seam is now typed correctly

The old Round-30 coordinate interface uses rational assignments. That is the right exact syntax for rational Galerkin coefficients, but it is not the complete trajectory carrier required by Picard--Lindelof. Round 34 already interpreted the same polynomial syntax on Murray--Bishop constructive reals, whose equality is a setoid relation rather than Agda propositional equality.

`NSTriadKNBishopSetoidCoordinateGluingRound36Exact` therefore defines the correct Bishop-real setoid coordinate equivalence. It requires genuine encode/decode round trips in the physical-state setoid and pointwise Bishop equality, plus coordinate reflection back to state equality. For any literal Galerkin representation it proves both faces of the vector-field square:

```text
encode(F_phys state) ~= F_coord(encode state),

F_phys(decode coordinates)
  ~=State decode(F_coord coordinates).
```

This removes the rational/completeness type mismatch without quotienting constructive-real equality by an unsafe axiom. The actual Fourier-state/Bishop-assignment codec and real Picard--Lindelof authority remain physical/analytic producers.

## Validation hardening

The Round-36 checker first executes the repaired Round-35 checker. It rejects holes, postulates, unsafe termination/positivity escapes, `funext`, `Properties.WithK`, `unique⇒irrelevant`, and module-local `--with-K`. Its cumulative Agda invocation goes through `scripts/agda29_without_k_wrapper.sh`, which supplies the global `--without-K` option to the same pinned Agda binary used by the repository checker.

The proof markers for the selection-rule tranche now require the actual shell-negation theorem, full `RetainedTriadMember` fields, and inhabited closure records. The unresolved physical producer markers remain false.

## Exact frontier after this round

The most informative new decision is negative and now quantitative: the mode-principal-angle HH-good route is blocked by a uniform `7/16` two-channel Gram-energy floor, not merely by one exceptional orthogonal pair. The two live HH-bad inverse-scale mechanisms are explicit and mutually checkable: one-derivative Schur elimination or a dissipative bad-stratum floor. `Com` is reduced to the literal operator realization of an exact increment/naturality defect. The finite shell and owner-budget limits now have coherent algebraic carriers; the nine-owner region has a robust/critical/infeasible classification; the active triad subgraph is cutoff-complete and carries all five physical selection requirements; and the finite-flow lane has a type-correct Bishop-real setoid seam rather than a rational surrogate.

None of these results is promoted to unconditional Navier--Stokes regularity. The physical PDE producers, actual Bishop-state coordinate codec, real Picard--Lindelof instance, actual transversality/reality/nonzero-coupling selection predicates, nine actual owner estimates, cutoff limits, compactness and continuation remain required.
