# Conscious-access Round Six: ternary/visual cross-pollination

Round Six joins the Round Three visual-morphogenesis/hall formalism to the
Round Five ternary/Yijing, braid, and neural-field formalism.  It introduces no
new claim that the Yijing, psychedelic perception, morphogenesis, or neural
measurement share one physical mechanism.

## Exact transition-system bridge

`TernaryVisualMotifSemiconjugacyExact.agda` defines the ternary phase cycle

```text
negative -> zero -> positive -> negative
```

and the projection

```text
negative -> lattice
zero     -> tunnel
positive -> face.
```

It proves the commuting transition equation

```text
motifOfTrit (ternaryPhaseStep t)
=
motifStep reweightedMotifRegime (motifOfTrit t)
```

for every trit, together with exact period three and injectivity of the finite
motif encoding.  Shared period remains weaker than shared mechanism.

## Morphogenetic field section

`TernaryMorphogeneticVisualFieldExact.agda` indexes the existing homogeneous,
square-mode, and branching-mode chemical states by balanced trits.  The map
from trit to field and back is an exact section:

```text
phaseOfField (fieldOfTrit t) = t.
```

The field then projects through the same motif map.  The construction reuses
the Turing, phyllotaxis, space-colonisation, and DLA provenance already carried
by `MorphogeneticVisualGenerator`.

## Neural observation quotient

`TernaryMotifNeuralObservationQuotientExact.agda` composes the ternary/motif
phase with the existing finite neural Laplacian carrier.  Negative and zero
phases have:

```text
same coarse fMRI-like observation,
different microscopic Laplacian variation,
different motif projection.
```

Thus coarse observation does not identify ternary phase, motif state, or
microscopic activation.

## Complementary braid-history witnesses

`TriadicVisualBraidCrossPollinationExact.agda` joins two logically complementary
cases:

1. the triadic Artin/Yang--Baxter paths have equal endpoints but distinct braid
   word residuals;
2. the visual completion/inhibition histories have the same component multiset
   but distinct endpoints and residual one.

Therefore neither endpoint equality nor component equality is sufficient to
erase path history.

## Ternary hall coalition

`TernaryHallTransitionCoalitionExact.agda` combines the existing hall-of-halls
candidate with the canonical moving-line cast.  The finite joint objectives are

```text
static architecture = 8
moving projection   = 6
integrated hall     = 0.
```

The integrated ternary hall is minimal over the declared canonical family.  A
zero model objective does not recover the remembered scene, and a moving cast
does not predict an external event.

## Provenance

`ConsciousAccessRound6CrossSourceBridge.agda` reuses four already attributed
records rather than manufacturing a new empirical source:

- Alan M. Turing, *The Chemical Basis of Morphogenesis*, DOI
  `10.1098/rstb.1952.0012`;
- Fan R. K. Chung, *Spectral Graph Theory*, DOI `10.1090/cbms/092`;
- Emil Artin, *Theory of Braids*, DOI `10.2307/1969218`;
- Richard Rutt, *Zhouyi: The Book of Changes*, no DOI recorded.

The source conjunction motivates typed interfaces only.  It does not prove a
shared mechanism or create new empirical evidence.

## Validation

The regression root is

```text
DASHI/Biology/ConsciousAccessRound6CrossPollinationRegression.agda
```

and the focused command is

```bash
bash scripts/check_conscious_access_round6.sh
```

The checker cascades through Round Five, rejects holes, postulates, unsafe
options, unsolved metas, and placeholder right-hand sides, then invokes the
pinned Agda 2.9 checker on both the Round Six regression and
`DASHI/Biology/Everything.agda`.
