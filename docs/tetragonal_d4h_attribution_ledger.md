# Attribution and proof-status ledger: tetragonal 4/mmm

## Sources, scope, and authority

1. **Established crystallography (not original to DASHI):** Hermann–Mauguin
   4/mmm and Schoenflies D4h denote the tetragonal ditetragonal-dipyramidal
   point-group class. The abstract isomorphism D4h ≅ D4 × C2, its 16 elements,
   orthogonal matrix realisation, and invariant polynomial theory belong to
   classical crystallography and invariant theory. Consult the International
   Tables for Crystallography / IUCr notation and established group theory.
   We do not assign these results to repository contributors.
2. **User-provided visual example:** screenshot of @fantasticfeldspar,
   Instagram short captioned 'Tetragonal Crystal Systems and Point Grou...';
   its creator supplies the visual example and symmetry annotations.
   No full post URL, recording date, specimen provenance, chemical analysis,
   diffraction pattern, or space-group determination has been supplied.
   Treat the diagram as a claimed teaching illustration, not a measurement.
3. **Pre-existing DASHI mathematical owners:** KleinGroupActionInvariantExact,
   FiniteSymmetryStabiliserExact, BalabanClayT4HyperoctahedralGridOrbitExact,
   and AltermagnetCrystalActionBridgeExact. Their exact names, source notices,
   and limitations stay attached; no authorship is reassigned by reuse.
4. **New DASHI additions on PR #1261:** finite integer matrix certificate,
   generator permutation action on 8 sites, normal-form (Quarter × Bool × Bool)
   model, finite action definitions, and this attribution ledger. These are
   implementations of known structures, not new crystallographic discoveries.

## Status hierarchy / non-promotion rules

- Screenshot: visual teaching claim only.
- External mathematical classification: established background theorem.
- Python certificate: exact computational validation of a finite enumeration.
  An execution result does NOT imply an Agda or Lean kernel proof.
- Agda files: explicit definitions and selected proof terms. Typechecking
  not established in this session; compile receipts must be preserved
  separately if acquired. No 'postulate' is introduced.
- Missing proof obligations: composition associativity, identity and
  inverses for normal-form group; cardinality 16 via enumeration;
  faithful site action and native GroupAction instantiation; theorem
  generating the full polynomial invariant ring; a Seitz/lattice extension.
- Specimen: external morphology, ideal point group, atomic symmetry and
  measured diffraction are distinct objects. No proof of observed point
  symmetry, chemical composition or space group is claimed.

## No-source-promotion / identity guardrails

The symbol D4 in other project branches is not sufficient to establish a
crystallographic carrier equivalence. Reuse requires an explicit typed
isomorphism. Sources citing each other do not become independent evidence.
Likewise algebraic correspondence, computational test, and physical
identification must remain independently attributed and typed.
