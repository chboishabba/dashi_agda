# Stage amplitude, witness-fibre selection, SSP15 spectra, and depth-two Moonshine residue

This note documents the extension tranche added after the initial balanced-stage and sporadic-Tarot implementation.

## Signed amplitude is a projection

A balanced three-line atom is retained as a literal pattern in `{-1,0,+1}^3`. Its signed amplitude ranges from `-3` through `+3`; a joined pair ranges from `-6` through `+6`.

The implementation keeps line order and pattern separate from amplitude. In particular:

```text
+++ -> +3
--- -> -3
+-0 -> 0
++0 -> +2
```

and all three permutations of `++0` have equal amplitude while identifying different unresolved coordinates.

## Complete Stage-5 branching

The primary Stage-5 configuration is:

```text
lower = +++
upper = ++0
amplitudes = 3 + 2 = 5.
```

Its exact residue/deficit profile is:

```text
mod 3: remainder 2, next-closure deficit 1
mod 6: remainder 5, next-closure deficit 1
mod 9: remainder 5, next-closure deficit 4.
```

Three constituent-level branches are represented:

```text
positive completion: ++0 -> +++ ; 5 -> 6 ; S2 -> S3
negative resolution: ++0 -> ++- ; 5 -> 4
withhold incomplete sheet: retain +++ visibly at 3 and carry ++0 as residual 2.
```

The final branch refines the existing visible `5 -> 3` transition. No irrep decomposition is used to generate this primary arithmetic; irrep structure remains downstream.

## Witness fibre before selection

A Stage-3 closure witness carries:

```text
frame
P affirmed
Q affirmed
S affirmed
proof that S synthesises P and Q.
```

All admissible witnesses are retained in a dependent fibre. A separate finite MDL policy scores frames by:

```text
description length
contradiction
overreach
omission
residual cost.
```

The concrete three-frame example has costs `2`, `7`, and `9`; the cost-2 frame is accompanied by an actual natural-number minimality proof. Selection does not erase the witness fibre and does not promote existence under one frame to universal truth.

## Rich SSP15 spectrum

The existing fifteen `MonsterPrimeLane` constructors are reused. Each enriched lane reading contains:

```text
prime lane
projected ternary pattern
signed amplitude
orbit type
stabiliser
status
visibility
transport status
valuation depth
residual code
orientation.
```

Two frames can share the same local `+++` closure while differing at the `p71` lane. Thus the SSP15 object is a multiscale symmetry-resolution spectrum of a frame, not the frame itself.

The source boundary is class-sensitive. The implementation does not claim that every Monster conjugacy class of order `p` has one identical `Gamma_0(p)^+` Hauptmodul. A Fricke/class witness would be required for such promotion.

## Integrated image-to-frame pipeline

The checked pipeline is:

```text
image receipts
-> six-line observation
-> candidate frames
-> local/gluing witness fibre
-> SSP15 spectrum
-> MDL/residual selection
-> selected frame.
```

The canonical image projection retains lower `+++`, upper `++0`, and total amplitude `5`. The unresolved line is recorded as an attention coordinate; no Tarot or hexagram prediction of its eventual sign is asserted.

The amplitude/internal-geometry distinction is also kept explicit. Equal scalar amplitude can coexist with different line geometry, just as a trace or central phase does not reconstruct Heisenberg/Weyl or normaliser geometry. The separate Monster-3B local-module intertwiner is not imported or fabricated in this stack.

## Depth-two nonary residue

The exact arithmetic layer proves:

```text
196884 = 3^11 + 3^9 + 2*3^3
196884 = 21876*9
196884 = 7292*27
196884 = 2430*81 + 54

196883 = 21875*9 + 8
196883 = 7291*27 + 26
196883 = 2430*81 + 53

54 = 6*9 = 2*27
53+1 = 54.
```

A division-free commuting-square record shares the same `2430` complete 81-block bulk and carries residues `54 -> 53` together with values `196884 -> 196883`.

The structured terminal candidate is:

```text
TerminalFibre54 = HexadicCarrier x NonaryCarrier
```

with cardinality `6*9=54`. A real equivalence between the complement of one distinguished product point and the repository's `ReducedMode53` remains an explicit obligation.

The repo's literal self-indexed tetration is also distinguished from product depth:

```text
9*9 = 81
self-indexed level two = 9^9.
```

Therefore the depth-two nonary product is not identified with literal nine-tetration.

## Sources

- Andrew P. Ogg, *Automorphismes de courbes modulaires*, Séminaire Delange–Pisot–Poitou 16 (1974–1975), Exposé 7, pp. 1–8, MR 417184; no DOI assigned.
- John F. R. Duncan and Ken Ono, *The Jack Daniels Problem*, Journal of Number Theory 161 (2016), 230–239, DOI `10.1016/j.jnt.2015.06.001`.
- J. H. Conway and S. P. Norton, *Monstrous Moonshine*, Bulletin of the London Mathematical Society 11 (1979), 308–339, DOI `10.1112/blms/11.3.308`.
- Richard E. Borcherds, *Monstrous Moonshine and Monstrous Lie Superalgebras*, Inventiones Mathematicae 109 (1992), 405–444, DOI `10.1007/BF01232032`.

These references ground the modular/Monster background only. The frame, MDL, divination, residual, and stage semantics are explicitly the repository's formal construction.
