# 10. G3 Filtered Structure and the Associated-Graded Quotient Gap

## 10.1 Control Frame

- O: Worker 3 owns this subsection only; the admissible decision surface is the
  Paper 1 docs draft, not the Agda code.
- R: refine the G3 exposition around finite support, filtered operator pieces,
  and the gap between a filtered prequotient surface and an associated-graded
  quotient closure.
- C: this section reads the manuscript draft, the formal-core G3 section, and
  current G3 identifier surfaces; it writes only this file.
- S: G3 has constructive finite-support subtraction support for selected
  operators and a selected associated-graded prequotient/projection surface.
  It does not yet have an accepted quotient carrier `F_n / F_{n-1}`,
  projection-respects-equivalence inhabitant, or global Schrodinger promotion.
- L: progress is ordered as filtered selected support, then cumulative
  filtration inclusion, then equivalence modulo the denominator filtration,
  then quotient carrier, then descended projection/bracket laws.
- P: present finite support as partial constructive progress and present the
  quotient layer as a real remaining obligation, not as a stylistic cleanup.
- G: no sentence in this section may state that G3 is closed unless the owning
  receipt surfaces prove the quotient/equivalence/norm-law obligations.
- F: the central gap is the kernel-equivalence theorem for quotient classes:
  the zero class must be exactly the denominator filtration piece, and that
  equivalence is not yet available as an accepted G3 quotient infrastructure.

## 10.2 Filtered Progress Is Not Yet Quotient Closure

The G3 operator lane should be described as a filtered construction with a
constructive finite-support core. The currently admissible positive statement is
that selected finite-support operators have certified subtraction support via
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionCertifiedSupport`,
with the support witness available at
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.selectedFiniteSupportOperatorSubtractionSupportWitnessFromCertified`
and packaged by
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.G3SelectedSubtractionCertifiedSupport`.
This is real mathematical progress: it gives a controlled class of operators
for which subtraction remains inside an explicitly witnessed finite-support
surface.

That progress should not be conflated with an associated-graded quotient. A
filtered object gives pieces such as `F_n`, or in the current selected Agda
surface
`SelectedFiltrationPiece n = Sigma WaveFunctionOperator
(SelectedOperatorP2Degree _ n)`. The associated graded layer requires quotient
classes of the form `gr_n(F) = F_n / F_{n-1}` in the current increasing-index
presentation. Under a descending-index convention the denominator may be called
the next filtration term instead; the obligation is the same: the denominator
piece must be exactly the kernel of the projection from the filtered piece to
its graded class.

The kernel-equivalence obligation is therefore not cosmetic. To use quotient
notation honestly, the paper needs the theorem usually summarized as

```text
[x] = [0]  iff  x lies in the denominator filtration piece.
```

In the current indexing this denominator is the previous cumulative filtration
used for `F_n / F_{n-1}`; in a descending-filtration exposition it is the next
filtration layer. Either way, this equivalence is what prevents quotient
classes from being merely labels. It proves that the quotient projection has
the intended kernel, that representatives differing by a denominator element
map to the same class, and that no additional selected operator is silently
collapsed to zero.

The current `DASHI.Physics.Closure.G3AssociatedGradedQuotientSurface` records
exactly this distinction. It constructs selected prequotient pieces and a
constructive cumulative-filtration inclusion, and it names
`G3AssociatedGradedProjectionInterface` as a projection-only target. But the
surface explicitly remains non-promoting: accepted equivalence modulo the
previous filtration, an accepted quotient carrier `F_n / F_{n-1}`,
projection-respects-equivalence, and the p2-indexed Poincare/Galilei
isomorphism API remain missing.

## 10.3 Why Finite Support Helps

Finite support matters because it supplies a constructive domain where operator
subtraction can be controlled without appealing to an arbitrary
`WaveFunctionOperator` support theorem. On this selected subtype, support
witnesses can be transported through subtraction, making it plausible to define
finite matrix-level norm, valuation, and filtration data. This is the right
kind of local evidence for a later graded construction: one first proves that
the relevant differences and brackets stay inside manageable support bounds,
then proves that the quotient relation and projection laws respect those
bounds.

The present receipts reach only the first part of that story. The global
arbitrary-operator support boundary remains
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingGlobalFiniteNonzeroMatrixSupportWitness`.
The valuation and norm-law boundary remains
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.exactRemainingDifferenceNormLawBlockers`,
with the first named missing law
`DASHI.Physics.Closure.G3P2LimitConvergenceSurface.missingSelectedOperatorDifferenceNormIndexLaws`.
Thus finite support should be written as constructive progress toward a
quotient-ready operator algebra, not as evidence that the quotient algebra is
already present.

## 10.4 Risk Notes

- Do not state that G3 closes, that the Schrodinger lane promotes, or that
  arbitrary `WaveFunctionOperator` values have finite support.
- Do not treat `G3AssociatedGradedProjectionInterface` as an accepted quotient
  construction. It is a projection-only target and non-promoting boundary.
- Do not write quotient notation without naming the missing
  kernel-equivalence obligation. The required statement is that the zero class
  is exactly the denominator filtration piece, not merely that a projection
  function can be named.
- Do not infer norm symmetry, rational-difference ultrametric closure,
  rescaling/min-shift closure, finite-support product support, or bracket
  support from subtraction support alone.
- The next promotable G3 step is not prose polish. It is an inhabited additive
  quotient primitive: selected zero-difference, negation and addition closure
  in the denominator filtration, accepted difference-image membership, an
  accepted quotient carrier, and projection/bracket descent laws.
