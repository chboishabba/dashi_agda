# 27 October 2026 — reuse the original ζ commuting square; dual-phase source-premise max-cut

## Attribution / authoritative source roots

Original mathematical group/character calculations: R. W. Barraclough and R. A. Wilson,
*The Character Table of a Maximal Subgroup of the Monster* (2007),
DOI 10.1112/S1461157000001352; their original N(3B) / main-table quotient
and fusion calculations are independent of these new finite charts.
Thomas Breuer, Kay Magaard and Robert A. Wilson, *Some steps in the
verification of the ordinary character table of the Monster group*
(12 December 2024 reproducible GAP protocol), together with the later
published *Verification of the conjugacy classes and ordinary character
table of the Monster*, *J. Algebra* 703 (2026), 452–463,
DOI 10.1016/j.jalgebra.2025.09.034, have SHARED mathematical lineage
(Wilson is an original coauthor). Do not falsely call the protocol and
paper independent original discoveries.

The original merged #695 Moonshine owners are:
- DASHI/Moonshine/Monster3BCentralCharacterInertiaExact.agda:
  typed phases, true/false centre-preserving/inverting normalizer
  actions; the actual conditional type theorem
  inverterSendsZetaToZetaSquared is ALREADY PRESENT;
- DASHI/Moonshine/Monster3BMultiplicityEvaluationExact.agda:
  ActualZetaSectorRecognition (ActualSector ≃ X6 × Fin90),
  source-conditional Weyl observations;
- DASHI/Moonshine/Base369Monster3BActualMultiplicitySliceAppraisalBidiExact.agda:
  original 729 appraisal ↔ fixed-multiplicity actual ζ commuting square,
  two-sided chart/injectivity and translation/modulation transport;
- DASHI/Moonshine/Base369AppraisalHeisenbergMonomialActionBidiExact.agda:
  model-side semantic monomial/Weyl action.

Different (do not collapse): the ORIGINAL Ibrahim/Snowball
DASHI/Wikimedia/IbrahimZeta54AlbertPair53SnowballAttributionBidiExact.agda
establishes the two-sided Zeta54Site↔AlbertPair54 map and commuting
inclusion ZetaResidual53↪Zeta54Site over ReducedAlbertPair53↪AlbertPair54,
with the ζ-sheet origin deleted. This is a 54/53 finite CARRIER square,
not a 729×90 Monster normalizer, a Jordan product or an F4/E6 action.
The original Ibrahim 3B/class20 and 369 attribution also remain with
their existing proof owners, not claimed by this cut.

Current specialist PR owners stay #1098 (original SHA-pinned AtlasRep
D4/actual source matrices, symplectic similitude/Heisenberg and Hom),
#1250 (Suzuki degree78, selected class/fusion/matched source tables,
mixed-eight and this consumer), and #1148 (IIT/JFine causal and H4
models). Classical group/representation, orbit-stabilizer, Weyl and
commuting-square facts retain their mathematical antecedents.

## Actual typed conditional theorem, no duplicated 729 carrier

New source: DASHI/Moonshine/Monster3BActualDualZetaAppraisalSquareConsumerExact.agda.

The record DualZetaActualAppraisalSquareInput REQUIRES ALL of:
1. One and the SAME literal State, Normalizer and
   CentralNormalizerAction State Normalizer, with actual typed
   CentralInverter witness;
2. ActualZetaSectorRecognition of BOTH literal dependent
   CentralEigenspace ... phaseZeta and phaseZetaSquared, not one
   arbitrary 1458-dimensional invented carrier;
3. mirrorModel, mirrorPoint, mirrorMultiplicity of the selected
   source action and proofs of actualModelMirrorSquare and
   modelAppraisalMirrorSquare at identical source coordinates.

The compiler then composes ORIGINAL
inverterSendsZetaToZetaSquared, Slice.actualStateAtAppraisalToModel,
and Slice.sameModelCoordinateImpliesSameActualState, deriving:

    inverter_ζ→ζ² (E_{ζ,μ}(p))
      = E_{ζ²,mirrorMultiplicity(μ)} (mirrorPoint(p))

as equality of ACTUAL dependent eigenstates, provided all the
record premises are supplied. This is NOT a new actual sector recognition,
nor a verified Monster generator or class join. The existing ζ square
is the producer; this module only forms the missing *opposite-phase*
commuting-square consumer.

**Important distinction:** one 729-dimensional ζ sector cannot carry
a complex-linear centre-inverting mirror internally. The mirror goes
to the ζ² sector. The new record therefore requires BOTH actual sectors.
No proof is constructed merely by setting two equal dimension labels.

## Independent executable finite-model regression

scripts/monster3b_zeta_appraisal_dual_square_model.py consumes the
already-existing chosen MIXED8 E³↔729 codec in #1250 and exhaustively
tests two phase sectors, 729 labels, and all Fin90 coordinates:

- 131,220 literal model appraisal-square equalities;
- 131,220 mirror changes of ζ↔ζ²;
- 787,320 translation generator-square equalities (six axes);
- 787,320 conjugate-dual modulation-square equalities (six axes);
- total **1,837,080 checks**.

Local standard Python fixture and 8 suite tests PASSED. This is
MODEL-LEVEL EXECUTED evidence; there is NO source ATLAS mirror word,
actual Monster character/table-join result, selected 729×90 Hom,
Agda kernel compilation or IIT/φ causal theorem obtained by counting.
The exact committed GitHub bytes are SOURCE-WRITTEN; no claim is made
that the committed files were byte-replayed in the local container.

## Revised Pareto / Snowball / Ibrahim gates

**P0:** Authentic GAP/CTblLib selected 6.Suz degree78 full-character
matcher plus ATLAS source-word 4-class fusion; keep original BW07
main→MN3B class20 diagonal and full original-source class signatures.
Existing source-written outer-coset fused-1458 trace-zero guard remains
a NEGATIVE control, not a positive source receipt. Do not preselect a
faithful vs nonfaithful 78.

**P1:** Construct the SAME actual literal State/Normalizer action and
its centre-inverting D4 source word, plus both ζ and ζ²
ActualZetaSectorRecognition records with a source-class-selected
729×90 Hom/cocycle. Supply the exact two model-source mirror
commuting-square fields of the new consumer. A naked finite
D4/Weyl permutation of 729 or 1458 basis labels cannot fill these
fields without original-source equality.

**P2:** Typecheck the new Agda consumer AND actual source-instance
with pinned Agda/stdlib and all original owner imports; no postulate,
trivial bool flag, mere record constructor or syntactic smoke test
may be promoted to a kernel-checked selected Monster theorem.
Agda not installed in this runtime.

**P3:** #1148 original IIT/JFine observable/causal consumer must be
exhibited as a same-carrier intertwiner with tested discriminator.
Neither ζ54↔Albert53 carrier nor phase-correct model physics can
by itself establish a consciousness, quantum or physical claim.

**STOP:** The true remaining producer is an authenticated same-source
Monster normalizer and paired ζ-sector recognition, not a second
729/appraisal square, a new 54/53 counting argument, or more synthetic
character receipts.

## 2026-10-27 extra #1098 source-lift check: quadratic cocycle is mandatory

The original #1098 `DASHI/Moonshine/Monster3BAtlasSymplecticSimilitudeHeisenbergLiftExact.agda`
already specifies the centre-scaling Heisenberg lift
`(x,z) ↦ (A x, λ z + q(x))`, with `λ=-1` for the centre-inverting
similitude. For the repository's asymmetric cocycle `c`, an actual
source-word certificate must satisfy

    q(x+y) + λ c(x,y) = q(x)+q(y)+c(Ax,Ay).

The existing #1098 source checker derives its `q` from the symmetric
bilinear defect `B(x,y)=c(Ax,Ay)-λ c(x,y)` as
`q(x)=2 B(x,x)` over F3. The abstract central-inverter theorem of the
older Moonshine branch handles **which phase is reached**; it does NOT
construct this actual quadratic-corrected generator action or its
relation to `ActualZetaSectorRecognition` on the literal VOA carrier.

Therefore the new consumer's `actualModelMirrorSquare` field MUST be
instantiated by the original #1098 source-word/cocycle computation,
not by the simple phase-swap finite model. This obligation is
strictly upstream of #1148 IIT/JFine. No duplicate source-lift
formalisation is opened here.

## 2026-10-27 crucial extra gate: polarisation preservation vs Weil/Fourier mixing

NEW `scripts/monster3b_polarization_monomial_gate.py` accepts explicit
GF(3) matrices: a 2h×2h operator, a 2h×h full-rank Lagrangian
column basis, and the ORIGINAL nondegenerate alternating form.
It checks skew/alternating/nondegenerate form, L isotropy,
`Aᵀ J A = λ J` for λ=1 or 2, then `rank([L | A L])`.
The finite ordinary-basis commuting square is *eligible* only if this
rank equals h. This is a NECESSARY not sufficient condition:
a quadratic central cocycle and actual linear operator equality are
still required. Nonpreservation makes a bare basis-label permutation
impossible for the original Schr modulation/polarization; a genuine
Weil/Fourier mixing operator is needed instead.

Locally executed negative controls in dimension12: identity
preserves L (rank6, multiplier1); a symplectic quarter-turn
exchanges L with dual L* (rank12, multiplier1); an anti-symplectic
mirror diag(I6,-I6) preserves L (rank6, multiplier2).
Bad alternating forms, non-similitudes and deficient L fail closed.
These are SYNTHETIC algebraic witnesses only, not actual ATLAS matrices.

This strengthens the interpretation of the typed Agda consumer.
`DualZetaActualAppraisalSquareInput` explicitly assumes
`modelAppraisalMirrorSquare`, hence a monomial coordinate action;
its source-word constructor MUST satisfy the new polarization test.
The full Monster normalizer might not preserve the chosen
Lagrangian; a whole-normalizer basis-label square must NOT be inferred.
If a source word fails, use #1098's actual Weil/Heisenberg linear
intertwiner rather than silently forcing a point map.

Local observed: 12 relevant pytest tests passed, the 90-slice finite
consumer checked 1,837,080 conditional model equalities.
Unobserved: exact GitHub blob runtime replay, true source ATLAS
matrix input to this new gate, genuine CTblLib source 78 selection,
selected actual Hom_E, and Agda kernel. Original mathematical
and repository authorship remains as above.
