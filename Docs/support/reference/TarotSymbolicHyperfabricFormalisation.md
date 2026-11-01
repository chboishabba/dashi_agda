# Tarot symbolic hyperfabric formalisation

## Scope

This tranche formalises the Rider--Waite--Smith tarot carrier as a finite,
randomised, spatially arranged symbolic language. It implements:

```text
meaning = card range x spread position x question x context x neighbours
```

The implementation does not treat a card keyword as a context-free fact and
does not import paranormal, clinical, recovered-memory, or external predictive
authority.

## Reused repository substrate

The tranche is deliberately thin over existing DASHI structures:

- `DASHI.Reasoning.TypedHyperfabricCore` supplies vertex/edge stalks,
  incidence restriction, provenance, salience, global-section and obstruction
  types.
- `DASHI.Interop.SensibLawResidualLattice` supplies `exact`, `partial`,
  `noTypedMeet`, and `contradiction`; spread tensions remain typed residuals
  rather than being narratively erased.
- `DASHI.Cognition.PNF.EventAlgebra` supplies candidate-validity and
  residual-to-comparison classification.
- `DASHI.Biology.AssociativeDivinationPNFExact` supplies the existing
  separation between structural claims, autobiographical hypotheses,
  therapeutic prompts, external predictions, and independently verified
  external events.
- `DASHI.Biology.DASHIYijingTernaryDivinationExact` remains a neighbouring
  structured-chance system. Tarot is not identified with the Yijing: its
  dynamics arise primarily from spread topology and image-rich semantic
  composition rather than a canonical line-change algebra.

## Implemented carrier

`TarotCarrierExact.agda` defines:

```text
MajorArcana : 22 constructors
Suit        : Wands | Cups | Swords | Pentacles
MinorRank   : Ace..Ten | Page | Knight | Queen | King
Card        : Major MajorArcana | Minor Suit MinorRank
Orientation : Upright | Reversed
```

Explicit enumeration proves:

```text
22 majors
4 suits
14 ranks per suit
22 + 4 * 14 = 78 cards
```

The canonical stable index is `0..77`; the King of Pentacles is index `77`.
Draw orientation is stored on a card token rather than treated as intrinsic to
the printed card.

## Complete semantic kernel

`TarotSemanticKernelExact.agda` contains one total pattern-matching clause for
every card in the 78-card carrier. Each card receives:

- a central upright range;
- a shadow/reversal range;
- a regime/local-process scale;
- a provenance receipt.

The Minor Arcana also retain the compositional factors:

```text
suit  -> semantic domain
pip   -> rough phase
court -> mode of agency
```

For example, the Knight of Cups is represented both by its specific meaning
range and by:

```text
Cups   -> emotion, relationship, imagination, memory, receptivity
Knight -> pursuing or mobilising
```

Reversal is not implemented as logical negation. The admissible lens family is:

```text
blocked | internalised | excessive | deficient | distorted | releasing
```

## Spread hyperfabric

`TarotSpreadHyperfabricExact.agda` represents a spread as typed positions and
relations. The canonical three-position layout uses:

```text
inheritance -> present constraint -> possible development
```

The final role is intentionally `possible development`, not a fixed future.

Draw-without-replacement is proof-relevant. The canonical Fool/Hermit/Tower
layout carries a recursive proof that indices `0`, `9`, and `16` are pairwise
distinct.

The spread instantiates the existing `TypedHyperfabric`:

```text
vertex stalk = local card/role/question/context reading
edge stalk   = transported relational reading
restriction  = incidence-indexed semantic transport
edge data    = provenance, salience, and residual level
```

A concrete hyperfabric obstruction retains a `partial` withdrawal/action
tension. Coherent interpretation does not imply residual erasure, and the
obstruction does not diagnose the querent.

## Associative PNF and bounded MDL

`TarotInterpretationPNFExact.agda` compiles a tarot interaction through the
existing associative-divination PNF. The canonical reflective trace compiles
exactly to:

```text
cast produced
participant association selected
autobiographical theme hypothesised
```

No external-prediction atom is generated.

Narrative candidates carry five finite penalties:

```text
description length
fit
contradiction
overreach
omission
```

The canonical compact interpretation has total cost `2`; a catastrophic
external-certainty overreading has cost `6`. A proof witness establishes
`2 <= 6`, while the rejected alternative remains present in the normal form.

`InterpretationNF` retains:

```text
selected narrative
alternatives
unresolved residuals
provenance
authority flags
normalisation receipt
```

The canonical authority flags assert reflective availability while denying
ancient-Egyptian origin support, future-causation proof, and clinical
diagnostic authority.

## Causal boundary

The formalisation separates two constructors:

```text
independently fixed outcome
reflective action intervention
```

and proves them unequal. A reading may alter later action; that path is not
relabelled precognition.

## Sources

The bounded source atlas records:

- Pamela Colman Smith and Arthur Edward Waite, the 1909
  Rider--Waite--Smith deck; no DOI assigned.
- Tim Husband, *Before Fortune-Telling: The History and Structure of Tarot
  Cards*, The Metropolitan Museum of Art, 2016; no DOI assigned.
- Matthew Prock, Ziv Epstein, Hope Schroeder, Amy Smith, Cassandra Lee,
  Vana Goblot, and Farnaz Jahanbakhsh, *Interpretive Cultures: Resonance,
  randomness, and negotiated meaning for AI-assisted tarot divination*,
  DOI `10.48550/arXiv.2602.11367`.
- Iulia Duta, Giulia Cassara, Fabrizio Silvestri, and Pietro Lio,
  *Sheaf Hypergraph Networks*, DOI `10.48550/arXiv.2309.17116`, imported
  only through the repository's existing typed-hyperfabric abstraction.

## Validation

Run:

```bash
bash scripts/check_tarot_symbolic_hyperfabric.sh
```

The checker:

1. requires all tranche files;
2. rejects holes, postulates, unsafe escapes, and placeholder right-hand sides;
3. checks that the semantic function has exactly 78 explicit card clauses;
4. guards the finite carrier, residual, alternative-retention, and
   authority-boundary declarations;
5. invokes the repository's pinned Agda 2.9 checker on
   `DASHI/Biology/TarotValidation.agda`.

A source citation or a successful finite regression is not promoted to proof
of divinatory efficacy.
