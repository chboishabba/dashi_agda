# Musical Symmetry As MDL-Dominant Basin Geometry

This note records the stronger target behind the earlier symmetry-biased toy.

The weak toy claim is:

`explicit symmetry reward + contraction -> symmetric basins dominate`

The stronger Dashi target is:

`MDL/compression + contraction -> symmetric basins dominate`

That difference matters. The first is a demonstration. The second is the start
of an explanation.

## 1. State Space

Let a melody be a finite pitch-class sequence:

`m ∈ (Z12)^n`

The repo toy works on small fixed-length melodies with pitch classes taken
modulo `12`.

## 2. Symmetry Transform

Fix a melody symmetry operator `S`.

Examples:

- reversal
- inversion
- retrograde inversion

The current toy implementation allows all three and defaults to reversal.

## 3. Flow

The contraction-style update moves each coordinate toward its symmetry partner
along the shortest cyclic path:

`x_{t+1} = flow_alpha(x_t, S(x_t))`

followed by a transposition-quotient canonicalization step.

The current toy keeps this deliberately simple:

- shortest cyclic displacement on `Z12`
- fractional move controlled by `alpha`
- integer rounding
- canonical transposition so the first note is `0`

## 4. Two Energy Modes

### Legacy symmetry-bias mode

The old toy energy is a direct asymmetry penalty:

`E_sym(m) = Σ_i d_Z12(m_i, S(m)_i)`

This can be converted into an explicit basin bias.

Useful as a control:

> if symmetry is directly rewarded, do symmetric basins dominate?

### MDL mode

The stronger toy replaces explicit symmetry reward with a compression proxy:

`L(m) = compression_cost(m)`

The current implementation uses a simple melody MDL proxy built from:

- distinct pitch classes
- distinct interval classes
- interval run count
- best exact repeating period
- residual mismatch to that best period

This is not a finished music-theoretic MDL. It is a first repo-local
compression proxy that does **not** explicitly encode symmetry as the target.

## 5. Basin Question

The actual research question is:

> when no explicit symmetry reward is used, do low-MDL attractors align with
> symmetry classes and dominate basin volume under the same contraction map?

That is what makes the MDL toy stronger than the symmetry-biased toy.

## 6. Theorem-Shaped Target

The real theorem target is:

### Musical Symmetry Target

Let `T = C ∘ flow` be a contracting melody operator, where `C` is a quotient
canonicalization map and `L` is a description-length functional.

Ask whether:

1. low-`L` attractors are concentrated in symmetry classes induced by `S`, and
2. the Monte Carlo basin volume of those attractors dominates without explicit
   symmetry reward.

If so, the repo has crossed from:

- "symmetry wins when rewarded"

to:

- "symmetry appears as a compression-favored attractor class"

## 7. Implementation Surface

The companion implementation is:

- [`scripts/musical_symmetry_mdl.py`](../scripts/musical_symmetry_mdl.py)

It provides:

- contraction flow on `(Z12)^n`
- symmetry-bias and MDL modes
- attractor search
- Monte Carlo basin estimates
- aggregate basin summaries for exact-symmetry mass and low-MDL mass
- JSON output for inspection

## 8. Not Claimed

This note does not claim:

- that the current MDL proxy is musically canonical
- that the toy already proves symmetry emergence in a theorem-grade sense
- that all symmetry classes must dominate under arbitrary contraction maps

It does claim that the correct next experiment is no longer the explicit
symmetry reward toy. It is the MDL toy.

## 9. Pitch-Class Carrier Bridge

The safe algebraic bridge for pitch classes is:

`Z/12Z ~= Z/3Z x Z/4Z`

by CRT, since `gcd 3 4 = 1`. This supports a triadic/quartic factor reading of
the 12-tone carrier, but it does not by itself prove a music theorem.

Do not state that the perfect-fifth shift gives a three-element orbit. The
perfect-fifth map is `x -> x + 7 mod 12`; since `gcd 7 12 = 1`, it has order
`12` and generates the full circle of fifths.

For the broader claim-boundary note, see
[`AntifascisticBoundaryAndMusic.md`](AntifascisticBoundaryAndMusic.md).

## 10. Musical Attractor Theorem Target

The named next bridge surface is
[`MusicalAttractorTheorem.md`](MusicalAttractorTheorem.md).

It sharpens the toy into a precise theorem-shaped construction:

- carrier: `C_n = (Z/12Z)^n`;
- metric: summed chromatic distance, not the DASHI prefix ultrametric;
- map: `K_music` as nearest-scale projection onto a chosen diatonic scale;
- Lyapunov level: `L_music` as total chromatic dissonance from that scale;
- certificate: one-step descent to the fixed set `S^n`;
- quotient discipline: keep CRT `p mod 3`, tonal cluster `floor(p/4) mod 3`,
  and perfect-fifth order-12 dynamics separate.

Claim level remains `exploratory/bridge` until a concrete Agda module is added
and checked.
