# Antifascistic Boundary Examples And Music

Declared surface level: `bridge/exploratory`.

This note records three adjacent examples that help explain the fascistic /
antifascistic split without promoting them into stronger theorem claims:

- antifascistic systems as invertible, entropy-preserving dynamics;
- the three-body problem as a carrier-level antifascistic / observable-level
  fascistic boundary example;
- music as an MDL/contraction toy over pitch-class sequences.

## Repo Owners

Primary code and docs:

- `AntiFascistSystem.agda`
- `FascisticSystem.agda`
- `Fascism_Tests.agda`
- `DASHI.Physics.ThreeBody.*`
- `Docs/MusicalSymmetryMDL.md`
- `Docs/MusicalAttractorTheorem.md`
- `Docs/MusicalMDLComparison.md`
- `scripts/musical_symmetry_mdl.py`

Adjacent / speculative music artifacts:

- `monster/MUSICAL_PERIODIC_TABLE.md`
- `monster/PROOF_TO_SONG_PIPELINE.md`
- `monster/MONSTER_WALK_SONG.md`
- `monster/circom/monster_walk_music.circom`
- `monster/MonsterLean/MonsterMusic.lean`
- `monster/MonsterLean/MusicalPeriodicTable.lean`

## Fascistic Versus Antifascistic

In the current repo vocabulary:

- `fascistic`: projection/contraction-style update, usually many-to-one or
  entropy non-increasing, useful for attractors and selection;
- `antifascistic`: invertible, entropy-preserving update, useful for unitary,
  Hamiltonian, or reversible dynamics;
- boundary case: a full carrier may evolve invertibly while a coarse observable
  projection loses information.

`AntiFascistSystem.agda` is still abstract and postulate-backed:
`entropy-preserved` and `non-collapse` are assumptions over the current
interface. `Fascism_Tests.agda` is therefore best read as a smoke/spec surface:
it records the intended incompatibility between unitary-like invertibility and
projection-only strict collapse, but it is not a full derived physics theorem.

Safe natural examples:

- quantum unitary evolution between measurements;
- classical Hamiltonian / symplectic dynamics;
- reversible cellular automata and reversible circuits;
- topological or winding-number preserving motion;
- exact gravitational many-body dynamics before coarse measurement.

## Three-Body Boundary Reading

The three-body lane is already repo-local under `DASHI/Physics/ThreeBody/`.
Its own comments are the right claim boundary:

- no closed-form solution claim;
- no global contraction claim;
- local energy/action surfaces;
- explicit `contractiveRegion / coneBoundaryRegion / nonContractingRegion`;
- basin-relative predictive horizon;
- boundary-generated branching and interference-style regime aggregation.

The useful DASHI reading is representation-dependent:

- carrier level: exact Hamiltonian three-body dynamics is antifascistic in the
  sense that the full state evolution is reversible/volume-preserving in the
  idealized model;
- observable level: coarse measurement, finite precision, and long-horizon
  chaos make the predictive description effectively fascistic because many
  fine-grained states collapse to the same practical forecast class.

This is not a contradiction. It is the same carrier/projection split used
throughout the repo: invertible dynamics on a rich state space can become
lossy after an observable projection.

## Music Lane Reading

The repo has two separate music tracks.

### Dashi MDL toy

`Docs/MusicalSymmetryMDL.md` and `scripts/musical_symmetry_mdl.py` define the
safe maintained toy:

- state: pitch-class sequence `m : (Z/12Z)^n`;
- quotient: transposition canonicalization;
- candidate symmetries: reversal, inversion, retrograde inversion;
- flow: move each pitch class toward its symmetry partner on the shortest
  cyclic path;
- modes: explicit symmetry bias versus an MDL/compression proxy;
- question: do low-MDL attractors align with symmetry classes and dominate
  basin mass without directly rewarding symmetry?

Claim level: `toy/exploratory`. The current compression proxy is useful, but
not a canonical music-theoretic code length.

`Docs/MusicalAttractorTheorem.md` now records the named theorem-shaped target:

- carrier: `C_n = (Z/12Z)^n`;
- contraction: `K_music` as nearest-scale projection;
- Lyapunov level: `L_music` as total chromatic dissonance;
- certificate: one-step descent onto `S^n`;
- boundary: no perception, uniqueness, Monster-prime, or canonical-physics
  claim.

### Monster music artifacts

The `monster/` tree contains a broader generative/speculative music lane:
Monster Walk song material, musical periodic-table notes, Lean files, Circom
music proof material, and generated prime-frequency outputs. Those are useful
artifacts, but they are not part of the DASHI canonical physics proof spine.

## Safe Algebraic Bridge For Pitch Classes

The safe statement about the 12-tone pitch-class carrier is:

```text
Z/12Z ~= Z/3Z x Z/4Z
```

by the Chinese remainder theorem, since `gcd 3 4 = 1`.

This gives a legitimate bridge from pitch classes into a triadic component and
a quartic component. It does not by itself prove a music theorem.

Avoid the stronger false shortcut:

```text
"the tonic-dominant-subdominant triad is the Z3 orbit under perfect fifth shift"
```

The perfect-fifth shift is `+7 mod 12`, and because `gcd 7 12 = 1` it has
order `12`, not order `3`. It generates the full circle of fifths, not a
three-element orbit.

## Theorem-Shaped Music Target

A defensible future target is:

```text
MusicalAttractorBridge:
  carrier       : (Z/12Z)^n
  quotient      : transposition / selected tonal equivalence
  K_music       : contraction toward a defended scale or symmetry surface
  L_music       : explicit code-length / MDL functional
  certificate   : K_music descends L_music or contracts a stated metric
  result        : named attractor classes plus basin-volume comparison
  non-claim     : no universal theory of music or perception
```

This would be a cultural/aesthetic domain instance of the origin thesis only
after the map, metric, MDL functional, and certificate are all explicit.
The current `MusicalAttractorTheorem.md` surface names those parts in prose; it
does not yet discharge the Agda proof obligations.

## Non-Claims

- The repo does not currently prove that natural Hamiltonian dynamics are
  universally antifascistic in all physical settings.
- The repo does not solve the three-body problem.
- The repo does not prove that chaos is literally entropy collapse at the full
  carrier level.
- The repo does not prove a music-theoretic law of consonance, diatonicity, or
  perception.
- The repo does not put the Monster music artifacts on the canonical physics
  theorem spine.
