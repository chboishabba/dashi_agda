# Musical Attractor Theorem

Declared surface level: `exploratory/bridge`.

This note records the precise theorem-shaped music construction currently
available as a design target for the repo. It is stronger and more explicit
than the older MDL basin toy, but it is not yet an Agda theorem and it is not
part of the canonical physics proof spine.

## Carrier

The carrier is the pitch-class sequence space:

```text
C_n = (Z/12Z)^n
```

An element `x = (x_0, ..., x_{n-1})` is a melody of length `n`; each `x_i` is a
pitch class `0..11`.

The safe CRT decomposition is:

```text
Z/12Z ~= Z/3Z x Z/4Z
phi(k) = (k mod 3, k mod 4)
phi^-1(a,b) = 4a + 9b mod 12
```

This yields:

```text
(Z/12Z)^n ~= (Z/3Z)^n x (Z/4Z)^n
```

The `Z/3Z` channel is a real algebraic factor, but it does not by itself encode
tonic/dominant/subdominant or the circle of fifths.

## Metric

The chromatic distance on one pitch class is:

```text
delta(a,b) = (a - b) mod 12
d_1(a,b) = min(delta(a,b), 12 - delta(a,b))
```

The lifted melody distance is:

```text
d(x,y) = sum_i d_1(x_i, y_i)
```

This is a genuine metric, not an ultrametric. The DASHI prefix-ultrametric
fixed-point argument is therefore not automatically available. The music lane
needs a Lyapunov/descent certificate instead.

## Scale Projection

Fix a target diatonic scale `S subset Z/12Z` with `|S| = 7`. For example,
C major is:

```text
{0,2,4,5,7,9,11}
```

Define nearest-scale projection:

```text
pi_S(p) = argmin_{s in S} d_1(p,s)
```

Ties are broken by the lower pitch-class value. The musical contraction map is
pointwise projection:

```text
K_music : C_n -> C_n
K_music(x)_i = pi_S(x_i)
```

## Lyapunov / MDL Level

The music MDL analog is total chromatic dissonance from the target scale:

```text
L_music,S(x) = sum_i min_{s in S} d_1(x_i,s)
```

Core properties:

- `L_music,S(x) = 0` iff `x in S^n`.
- `L_music,S(K_music(x)) = 0` for all `x`.
- `K_music` is idempotent: `K_music(K_music(x)) = K_music(x)`.
- If `x notin S^n`, then `L_music,S(K_music(x)) < L_music,S(x)`.

This gives a one-step collapse onto the fixed set `S^n`. It is a retraction,
not a general ultrametric contraction theorem.

## Attractor Classes

Let `ScaleFamily` be the 24 major/minor diatonic scales:

```text
S = {S_0^maj, ..., S_11^maj, S_0^min, ..., S_11^min}
```

Each scale defines:

```text
A_S = S^n
```

The full attractor surface is a family of fixed sets:

```text
A = disjoint-tagged union_{S in ScaleFamily} A_S
```

The tag is important because different scales overlap as pitch-class sets; the
repo should not pretend the raw carrier points are disjoint when the musical
scale interpretations are not.

Transposition orbits give the two coarse class families:

```text
[S_0^maj] = {S_k^maj : k in Z/12Z}
[S_0^min] = {S_k^min : k in Z/12Z}
```

## Quotients

The CRT `Z/3Z` projection is:

```text
q(p) = p mod 3
```

Its fibers are:

```text
q^-1(0) = {0,3,6,9}
q^-1(1) = {1,4,7,10}
q^-1(2) = {2,5,8,11}
```

This is an augmented-triad / whole-tone-layer projection, not a major-scale
classifier. C major projects to:

```text
{0,2,4,5,7,9,11} -> {0,2,1,2,1,0,2}
```

That multiset is not a clean uniform major-scale invariant.

A separate tonal-cluster map can be named:

```text
q_5(p) = floor(p / 4) mod 3
```

with fibers:

```text
{0,1,2,3}    -> 0
{4,5,6,7}    -> 1
{8,9,10,11}  -> 2
```

This can serve as a coarse tonic/subdominant/dominant-style partition only after
its interpretation is stated. It is not the CRT `Z/3Z` factor and should not be
treated as a group homomorphism from `Z/12Z` to `Z/3Z`.

The perfect-fifth shift remains:

```text
p -> p + 7 mod 12
```

Since `gcd(7,12) = 1`, it has order `12`; it does not generate a three-element
orbit.

## Agda Target Signature

A future formal module should declare this as a bounded music island, not as a
physics-closure theorem:

```agda
module Music.MusicalAttractorTheorem where

MusicalCarrier : Nat -> Set
MusicalCarrier n = Vec (Fin 12) n

chromatic-dist : Fin 12 -> Fin 12 -> Nat
melody-dist    : {n : Nat} -> MusicalCarrier n -> MusicalCarrier n -> Nat

DiatonicScale : Set
DiatonicScale = Vec (Fin 12) 7

nearestScaleNote : Fin 12 -> DiatonicScale -> Fin 12

K-music : {n : Nat} -> DiatonicScale -> MusicalCarrier n -> MusicalCarrier n

L-music : {n : Nat} -> DiatonicScale -> MusicalCarrier n -> Nat

K-music-idemp :
  forall S x -> K-music S (K-music S x) == K-music S x

K-music-descent :
  forall S x -> L-music S (K-music S x) == 0

K-music-strict :
  forall S x -> L-music S x > 0 ->
  L-music S (K-music S x) < L-music S x
```

Before this becomes code, the repo needs a concrete `Fin 12` encoding, a scale
validity proof with distinct elements, and a total tie-breaking definition for
`nearestScaleNote`.

## Non-Claims

- This does not explain music perception.
- This does not prove the diatonic scale is uniquely MDL-minimal.
- This does not connect `Z/12Z` pitch classes to the Monster primes
  `{47,59,71}`.
- This does not identify `L_music` with `DynamicalClosure.mdlLevel`; it is only
  structurally analogous.
- This does not put music on the canonical physics proof spine.

## Current Repo Relationship

The existing executable toy remains:

- [`scripts/musical_symmetry_mdl.py`](../scripts/musical_symmetry_mdl.py)

The existing note remains:

- [`MusicalSymmetryMDL.md`](MusicalSymmetryMDL.md)

The new target here is narrower and cleaner: it names a concrete carrier,
metric, projection, Lyapunov function, attractor family, quotient distinction,
and formalization boundary.
