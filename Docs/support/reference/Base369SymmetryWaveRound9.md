# Base369 symmetry, quotient geometry, and continuous symbolic coding — Round 9

Round 9 implements the exact part of the attached step-state symmetry, 3/6/9 horizon, coarse/fine, p-adic-address and continuous/wave analysis without promoting heuristic analogies to physical or representation-theoretic claims.

## 1. Signed membership is not a Boolean complement

`Base369SignedMembershipExact.agda` now proves that the ordinary `isGood : SignedMembership -> Bool` projection sends both the true inverse class and the exterior/unclassified class to `false`, while those source constructors remain distinct.

Thus

```text
not member of Good
```

does not entail

```text
member of semantic inverse.
```

The local balanced trit is therefore an orientation observer over a richer fibre, not merely a three-valued spelling of `Bool`.

## 2. 3/6/9 is cumulative retained depth

`Base369LayeredAttractorAndCoarseFineExact.agda` makes the filtration executable:

```text
Horizon3
Depth6 = Horizon3 x Horizon3
Depth9 = Depth6 x Horizon3
```

with projection-after-extension theorems.  Refining from 3 to 6 or from 6 to 9 retains the earlier state.

The same module constructs a literal attractive-dead-end witness:

```text
immediate = (+,+,+)
medium    = (-,-,-)
long      = (-,-,-)
```

and separately proves that a branch may be complete at depth 3 while depths 6 and 9 remain open.

This is the exact typed form of:

```text
immediate success != durable attractor compatibility.
```

## 3. Structural 11 and semantic two-ones remain independent

The structural carrier is

```text
CoarseFine11 Coarse Fine = one coarse value + ten fine values
```

and the coordinate count is proved equal to 11.

Inside the coarse semantic channel, `NominalActual A` may independently distinguish declared and realised state.  A concrete witness has

```text
nominal coarse = positive
actual coarse  = adverse
all fine slots = adverse.
```

Therefore the `1+10` resolution decomposition and the `declared/actual` two-channel distinction coexist without being identified.

## 4. Depth-wise addresses and exact local-versus-propagated symmetry

`Base369AddressSymmetryAndBranchGeometryExact.agda` retains the dependent address-transport and operator/propagation equivariance interfaces and adds an exact finite prefix-depth function for ternary trajectories.

For every finite ternary path `a`,

```text
sharedPrefixDepth a a = depth(a).
```

This is the discrete exponent needed for the usual 3-adic-style statement that longer common prefixes represent finer address agreement.  Round 9 does **not** claim a completed p-adic field or a real-valued metric implementation.

The module also constructs a local swap-equivariant operator and a context-sensitive propagation for which the corresponding propagated square provably fails to commute.  Local symmetry therefore does not erase authority/capacity/context asymmetry.

## 5. Tree, DAG and braid are distinct projections

The existing generic carriers are retained:

```text
OpenHoleTree
ProvenanceDAG
ConstrainedBraid
```

and Round 9 adds concrete mathematics rather than only records:

- a diamond DAG in which two distinct middle histories reach the same join node and every edge advances a finite rank;
- adjacent swaps `sigma1` and `sigma2` on a three-strand carrier;
- involutivity of both swaps;
- the Artin braid relation

```text
sigma1 sigma2 sigma1 = sigma2 sigma1 sigma2
```

by computation.

The intended reading remains projection-dependent: unresolved holes are tree-like; identified continuations are DAG-like; distinct but mutually constrained trajectories are braid-like.

## 6. Exact step-state symmetry is richer than a trit itinerary

`Base369StepStateSymmetryQuotientExact.agda` defines an enhanced step state carrying:

```text
orientation
refined zero
liveness
servicing cost
attractor drift
boundary state
```

and an indexed exact stepwise correspondence.

A computable discrepancy sums mismatches across these fibres.  The file constructs two one-step trajectories whose bare trit projections are identical while their enhanced discrepancy is exactly 1 because servicing cost differs.

Thus

```text
same ternary signature
```

does not imply

```text
same process-bearing branch.
```

The module also gives a time-local quotient example: two nominal histories occupy one coarse orbit and then split into two refined orbits after context is exposed.

## 7. Effective diversity and servicing multiplicity are distinct

`Base369ProcessBranchAttractorExact.agda` now contains a concrete duplicate-branch quotient:

```text
nominal branches     = 2
effective orbit count = 1
operational copies    = 2.
```

This formalises the distinction between dynamical redundancy and operational redundancy.

It also adds a proof-bearing marginal budget

```text
gain = attractor + information + independent robustness + constructive interaction
loss = servicing + diversion + interference + redundancy
```

where a positive branch-addition certificate carries an exact natural-number slack.  The concrete example has total gain 7, total loss 3, and strict slack 4 expressed as `suc 3`.

A second witness fits within finite servicing capacity while an aligned and an adverse direction cancel to the neutral trit.  Therefore capacity sufficiency alone does not entail attractor progress.

## 8. Continuous and wave-valued carriers are preserved, not discretised away

`Base369WaveContinuousSymbolicCodingExact.agda` defines

```text
SymbolicCoding Carrier
EncodedState coding
```

where an encoded state stores both the exact carrier state and its SSP-trit observer value.  The theorem

```text
decode (encode coding x) = x
```

is generic in `Carrier`.

So the ternary state is a symbolic/address coordinate while the payload may be continuous, wave-valued, operator-valued, distributional, finite-dimensional or infinite-dimensional in later instantiations.

The same module adds multiresolution coefficient cells retaining exact coefficient values together with `(scale, position, trit)` addresses, and generic balanced odd alphabets with exact slot counts

```text
3, 5, 9
```

for the ternary, quinary and nonary cases.

It also gives a structural coarse/fine witness with positive coarse observation and adverse fine channels, proving by construction that coarse affirmation does not force fine attractor alignment.

## Sources

- Emil Artin, **Theory of Braids**, *Annals of Mathematics* 48 (1947), 101–126. DOI: `10.2307/1969218`.
- Jean-Pierre Serre, **A Course in Arithmetic**, Graduate Texts in Mathematics 7, Springer. DOI: `10.1007/978-1-4684-9884-4`.
- Ingrid Daubechies, **Ten Lectures on Wavelets**, CBMS-NSF Regional Conference Series in Applied Mathematics 61, SIAM, 1992. DOI: `10.1137/1.9781611970104`.

The sources support the standard braid, p-adic and wavelet background.  The Base369 synthesis and its typed interfaces are repository-original constructions.

## Explicit non-promotions

Round 9 does not claim that:

- the discrete prefix exponent is itself a completed 3-adic analytic theory;
- the finite discrepancy is the real-valued exponential similarity kernel;
- a ternary symbolic coding makes an arbitrary payload discrete;
- a tree, DAG or braid is the unique global ontology;
- Base369 address symmetries are automatically Monster, physical, legal or psychological symmetries;
- a positive coarse observation forces fine or long-horizon success.
