# Original SU(2) Wilson model: volume-uniform high-beta plaquette-deficit theorem

Date: 9 November 2026. Source-specific analytic result, **not** a Clay theorem, **not** a full-Wilson spatial clustering estimate, and **not** yet an Agda-kernel-certified selected Wilson theorem.

## Theorem (original periodic SU(2) Wilson measure)

Let a four-dimensional periodic hypercubic lattice have V sites, L=4V oriented positive links and P=6V unoriented plaquettes, with normalized product SU(2) Haar measure and Wilson partition function

`Z(β)=∫ exp(β Σ_{p} t(U_p)) ∏_{links} dH(U_l)`, `t(U)=(1/2) Re Tr(U)`, `β≥16`.

Write `p_V(β)=(1/P) log Z(β)`, and `d_p=1-t(U_p)`. Then every finite periodic volume obeys the *same* bound

```
0 ≤ E_β[d_p] = 1 - p'_V(β)
  ≤ (8 + (2/3) log 24 + log β)/β,
```

for every plaquette p, by lattice translation/rotation symmetry. In particular the expected plaquette deficit tends to zero as β→∞ **uniformly in the number of periodic cells**. At a specified positive link, define its six-plaquette deficit `D6=Σ_{p adjacent to l} d_p`, and the six original oriented-staple sum `S=Σ_j V_j`, `R=||S||`. Then

```
E_β[D6] ≤ 6 (8 + (2/3) log 24 + log β)/β

P_β(R<r) ≤ 6(8 + (2/3) log 24 + log β) / (β (6-r))

P_β(t(U_l V_staple)≤0)
  ≤ 6(8 + (2/3) log 24 + log β) / (β (6-r))
     + 3 exp(−βr/2),          0<r<6.
```

The last line combines the already established original one-link conditional SU(2) Haar bound in `YMClaySU2OriginalOneLinkCoherentStapleTail20261109.md` with the previous pointwise `D6≥6-R` and the new pressure result. Its first contribution is **O(log β/β)** in every volume, not an unproved expectation socket.

## Proof — partition lower bound with explicit SU(2) geometry

1. Every SU(2) element is a unit quaternion `U=cos θ + n sin θ` with geodesic distance `θ∈[0,π]` to the identity, and normalized Haar radial density `(2/π) sin² θ dθ`. For `δ=β^(−1/2)≤1/4`, the Haar mass `m_δ` of the ball `θ≤δ` satisfies
   `m_δ = (2/π)∫_0^δ sin² θ dθ ≥ 8δ³/(3π³) ≥ δ³/24`.
   The first inequality is `sin θ ≥ 2θ/π` for `0≤θ≤π/2`; the second follows from `π≤4`.
2. Restrict the original normalized **product Haar integral** to the event `A_δ` that all `L` original link matrices lie within the SU(2) identity ball of radius δ. Its exact Haar probability is `m_δ^L`. The bi-invariant geodesic triangle inequality implies each four-factor oriented plaquette product has geodesic distance at most `4δ≤1` from identity. Therefore `t(U_p)=cos θ_p≥cos(4δ)≥1−8δ²`.
3. On `A_δ`, `Σ_p t(U_p)≥P(1−8δ²)`. The original partition function, without any gauge fixing or modifying the action, consequently satisfies
   `Z(β)≥m_δ^L exp(β P(1−8δ²))`.
   Divide its log by `P`, use `L/P=2/3`, and substitute δ²=1/β:
   `p_V(β) ≥ β−8−(2/3)log24−logβ`.
4. The finite-volume pressure `p_V(β)` is smooth and convex because the source is a finite compact-group Haar integral and `p''_V(β)=Var_β(Σ_p t(U_p))/P≥0`. Since normalized Haar has `Z(0)=1`, we have `p_V(0)=0`. Convexity yields
   `p'_V(β)≥[p_V(β)−p_V(0)]/β=p_V(β)/β`.
   Combining with step 3,
   `1−p'_V(β) ≤ [8+(2/3)log24+logβ]/β`. This is the expected average deficit `(1/P)Σ_p E_β[d_p]`. Translation and orientation symmetry of the periodic Wilson action make each plaquette expectation identical.
5. Sum over the six adjacent original plaquettes to bound `E_β[D6]`. The earlier exact pointwise action `D6≥6-R` gives `1_{R<r}≤D6/(6-r)` for `0<r<6`. Take original-measure expectation, then add the known conditional Haar tail. No stochastic independence, RG approximation, gauge variant expectation equality, or small-field truncation has been used.

## What this does and does not pay

**Paid analytically, pending native Agda formalization:** an explicit β-dependent **volume-uniform** local original SU(2) Wilson plaquette and frustrated-staple suppression bound. In particular the previous bound requiring an unknown `E[D6]` has been replaced by a closed elementary function of β for β≥16.

**Not paid:** the β-versus-lattice-spacing renormalized scaling trajectory, per-*physical*-block control of the growing number of links, a bound on spatially *connected* bad-field polymers with entropy, CMP116 applicability on original marked directions, long-distance full Wilson covariance clustering, original interacting R4 Schwinger limits, positive same-H spectral gap, continuum nontriviality or extension to all compact simple G. Union-bounding O(a^{-4}) individual link failures is not enough when β(a) grows slowly. The shrinking of the bare plaquette expectation toward 1 alone does **not** prove or disprove continuum nontriviality.

**Numerical/finite regression:** `scripts/check_ym_su2_original_wilson_pressure_uniform_20261109.py` independently checks algebraic parameter ratios and exact-rational quaternion plaquette triangle/deviation witnesses. It is an independent negative/finite control, not an integration or Agda-kernel proof. Attribution: original Wilson finite-lattice action, SU(2) Haar/quaternion geometry, elementary finite-volume Gibbs pressure convexity; DASHI combines these with the existing actual conditional one-link source.


## Further theorem: volume-uniform fraction-of-bad-plaquettes control

The same **original** finite Wilson probability measure gives a stronger *bulk-density* statement without assuming independence. Fix `0<ε≤2` and let `B_ε(U) = # {p : 1−t(U_p)≥ε}/P`, the proportion of plaquettes with deficit at least ε among all `P=6V` unoriented plaquettes. The pointwise bound `ε·1_{d_p≥ε}≤d_p` gives `ε·B_ε(U)≤(1/P)Σ_p d_p`. For β≥16, the pressure theorem thus yields

```
E_β[B_ε] ≤ [8+(2/3)log24+logβ]/(βε).

P_β(B_ε≥η) ≤ [8+(2/3)log24+logβ]/(βεη),
                                             η>0.
```

These inequalities hold **uniformly over the periodic finite volume** and make no assumption that bad plaquettes are independent. They establish that the expected density, and the probability of a fixed positive density, tends to zero as β→∞. The second is Markov's inequality on a nonnegative physical observable.

**Sharp limitation:** density control is not connected-polymer control. On an `n×n×n×n` periodic torus, a geometrically traversing connected path of `n` distinct bad plaquettes can occupy a fraction `n/(6n⁴)=1/(6n³)` of all plaquettes. This tends to zero, so vanishing bad-plaquette density permits arbitrarily long sparse connections. An actual Peierls/polymer activity or block mixing estimate must bound *connected bad supports*, rather than just `B_ε`. Neither E1 continuum convergence nor D1 full covariance clustering follows from this density theorem.
