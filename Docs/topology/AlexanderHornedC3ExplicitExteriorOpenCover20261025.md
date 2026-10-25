# Alexander horned C3: an explicit open cover on the SAME exterior (2026-10-25)

## Attribution and scope

Classical mathematical roots: J. W. Alexander, horned sphere (1924);
A. Hatcher, *Algebraic Topology*, Example 2B.2, printed pp.170–172,
https://pi.math.cornell.edu/~hatcher/AT/AT.pdf (his original punctured
torus attachment and commutator exterior tower); F. Lippert, *The
Alexander Horned Sphere and Bing's Hooked Rug*, supported horn-stage
exposition; classical tame Schoenflies and van Kampen. The three
rational centres/radii and this particular cover are repository-derived,
NOT claims of priority over these source constructions.

Existing proof owners reused:
`proofs/horned_c3_lean/HornedC3/ThreeArmVanKampen.lean`,
`ThreeArmCollarIntersections.lean`,
`ThreeArmCollarCoverAssembly.lean`,
`ThreeArmCentralPi1Reduction.lean`, and the pinned
Deicyde/hatcher-at `OverlapGroup` based fundamental group. Avoid
building another abstract free-product construction.

## Actual, not hypothetical, open sets

Work in the *actual* subspace `E=R^3 \\ B`, where B is the
three-sector closed wild solid once supplied by the chosen supported
Alexander/Hatcher model. Define
`c_0=(9,0,0), c_1=(0,9,0), c_2=(0,0,9)`, and
`r_-=15/4, r_+=17/4`. Then define

```text
C   = { x in E : for every i, |x-c_i| > r_- }.
S_i = { x in E : |x-c_i| < r_+ }.
U_i = C union S_i.
```

All are relatively open in E, without any assumption about the
complicated local wild surface. This is a genuine choice of sets,
not a schema awaiting an unknown open cover. The following are exact:

* `|c_i-c_j|²=162`, while `(2r_+)²=289/4 < 162`.
  Hence `S_i ∩ S_j = empty` for distinct sectors.
* Since `r_- < r_+`, each `x∈E` belongs either to C,
  or to some inner closed cut ball `|x-c_i|≤r_-` and hence S_i.
  So `E=U_0∪U_1∪U_2`.
* Therefore `U_i∩U_j=C` for i≠j, exactly the existing
  Lean intersection lemma's hypothesis; triple intersections with at
  least two distinct indices are also C.
* `x_0=(20,20,20)` is a rotation-fixed point of E outside the
  satellite cut balls and lies in C provided B is inside the
  displayed central/tube/satellite envelopes.

`scripts/alexander_horned_c3_explicit_open_cover.py` audits the
radius separations and all cut-sphere/tube containment margins over
rational numbers. This calculation relies on universal triangle/
coordinate inequalities, NOT random finite samples.

## Strongest next geometric deduction: C has no wild satellites

Assume the SAME-OBJECT source construction guarantees that every
wild satellite `B_i` is contained in its unit-radius reference
ball around c_i, and the only remaining solid outside those unit
balls is the central round unit ball and the three straight,
radius-1/4 tubular spokes (the assumptions of the existing gluing
geometry). Since `1<r_-`, all wild satellites lie inside the
closed inner cut balls. Thus

```text
(R³ \\ B) ∩ intersection_i { |x-c_i| > r_- }
    = R³ \\ K,
K = central closed ball union three straight tubes
    union three closed radius-r_- cut balls.
```

Here K is a *finite tame model*, not the original wild B. Each
straight spoke joins the central round ball to exactly its own
inner cut ball, meets no foreign cut ball or other spoke, and has
a collared disk end (the same exact cylinder/sphere inequalities).
K is a tame regular neighbourhood of a three-edge star, hence a
topological closed 3-ball by the classical tree regular-neighbourhood
construction. Its exterior in R³ has trivial pi1 by tame Schoenflies;
its H2 is Z, so **do not claim C is contractible in R³**. In S³ the
corresponding exterior with infinity included is an open 3-ball.

This supplies a PAPER-LEVEL argument for `pi1(C)=1`, conditional
only on the actual wild satellite staying inside its reference
envelope and on the standard tame-tree neighbourhood theorem.
It does not install a Lean `Subsingleton (FundamentalGroup C x0)`
instance: the needed ambient equivalence maps have not yet been
encoded and compiled.

## Remaining satellite-side acceptance

The honest annular overlap in one satellite is

```text
C ∩ S_i = {x∈E : r_- < |x-c_i| < r_+}.
```

(The other inner balls cannot meet S_i by centre separation.)
It is a finite radial shell with a single straight cylindrical
spoke removed. A source-specific explicit radial collar
trivialisation should identify it with (open disk) × interval;
the previous radius-4 stereographic atlas is one cross-section,
not by itself the full shell trivialisation.

Then establish in the same E:
(1) the relative collar homotopy equivalence of satellite S_i
with the corresponding Hatcher exterior G_A;
(2) the van Kampen inclusion-induced identification of each U_i
with G_A via central C and the shell overlap;
(3) C3 naturality of the three inclusion maps.

The current **open-set, coverage and disjointness gates are now
mathematically discharged** by explicit universal inequalities.
Central simple connectivity has a tame-tree classical argument,
not a kernel proof. The satellite-side full geometric equivalences,
the actual infinite wild embedding formalisation, and the exact-head
Lean/Agda typechecks remain separate open gates. Do not promote
these distinctions.

## Pareto, snowball, Ibrahim next-cut order

Highest return per work: finish the one radial-shell product
homeomorphism and the relative satellite cap slide, then connect
these to the EXISTING Lean `ThreeArmCentralPi1Reduction`.
Do not repeat established Ore finite quotient machinery, unrelated
p-adic/VOA actors, or the already implemented gauge simulator.
Source-follow only the actual topological hypotheses in Hatcher,
supported horn discussions, and a trustworthy tame-neighbourhood
theorem. Preserve the distinction between original mathematical
authorship, repo adaptation, source-written code, compiler receipt,
simulation and experimental measurements.
