# NS/Luo physical conditional continuation — round 17

This tranche advances the finite/Galerkin theorem surface into a physical
conditional continuation route and a separate integrated high–high absorption
route.

## Concrete mathematics added

1. **Direct torus trigonometric-polynomial carrier.** A finite polynomial is a
   list of physical character modes and complex coefficients. Character
   orthogonality and linearity of the normalized integral now imply coefficient
   extraction by an explicit induction over that list. The result no longer
   asks an arbitrary cyclic primitive root to stand in for the continuum torus.

2. **Fourier differentiation.** The exact complex multiplier algebra proves
   that two applications of `i k_j` give `-k_j²`, and summing the three second
   derivatives gives the Laplacian multiplier `-|k|²`.

3. **Centered commutator assembly.** The paired second-difference and
   derivative-variation branches are summed against the kernel second moment.
   A second induction proves the exact `2^{-2q}` moment scaling as
   `quarterPower q`.

4. **Galerkin tails and nonlinear projection error.** The weighted finite tail
   theorem proves the generic form of
   `||(I-P_N)u||_{H^m}² <= N^{-2(s-m)}||u||_{H^s}²`. The tensor identity
   `u⊗u-v⊗v=(u-v)⊗u+v⊗(u-v)` and its finite squared estimate are proved
   separately.

5. **Physical conditional continuation.** The existing annular four-class
   estimate is supplied at every Galerkin cutoff. A selected-subsequence error
   tending to zero and an explicit positive threshold margin yield the physical
   continuation inequality. This is a conditional physical theorem, not an
   unconditional regularity claim.

6. **Directional defect and integrated high–high absorption.** The unit
   directional Gram identity is lifted to physical vorticity amplitudes:
   `|ω_x×ω_y|²=a²b²Θ(ξ_x,ξ_y)`. Duration-weighted good cells are pointwise
   absorbed; bad cells are controlled by an amplitude cap and total residence
   charge. Finite summation proves the integrated absorption inequality.

7. **Nonlinear limit audit.** An exact four-point periodic countermodel has
   zero linear mean for each oscillatory factor but nonzero cubic transfer.
   Therefore linear coefficient convergence alone cannot justify passage of the
   cubic interaction to the limit.

## Source authority

The integrated absorption lane records both:

- Shin-ichi Inage, *Conditional Regularity of the Three-Dimensional
  Navier–Stokes Equations via High–High Triadic Absorption*, preprint DOI
  `10.20944/preprints202603.1591.v1` (non-peer-reviewed); and
- Shin-ichi Inage, *Structural Reduction Framework and Residence-Time
  Compression of Coherent Same-Scale Triadic Interactions in the 3D
  Navier–Stokes Equations*, DOI `10.3390/math14091410`.

The code keeps pointwise absorption, integrated absorption, and the
Constantin–Fefferman directional defect as distinct theorem strengths.

## Remaining frontier

The conditional physical route now has an exact formal endpoint. Unconditional
regularity still requires physical producers for the analytic inputs, especially:

- normalized Haar realization of the direct torus carrier;
- the continuum Hölder–Minkowski and Sobolev product estimates behind the
  centered commutator envelopes;
- a Navier–Stokes proof of residence-time compression or an equivalent
  integrated high–high absorption theorem;
- compactness or compensated structure strong enough to identify the cubic
  transfer in the Galerkin limit.

Those obligations are exposed at their genuine analytic boundaries rather than
being reported as already proved.
