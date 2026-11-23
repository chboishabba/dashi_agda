# Semantic naming migration inventory

This inventory records repository-wide scope after the Wilson Yang–Mills pilot.
It is an audit surface, not permission to mechanically rename every historical
source file.

## Current counts

Excluding generated, vendored, archive, provenance, and build output:

- Agda: 3,388 live module filenames containing `RoundNNN`, `roundNNN`, or an
  `RNNN` token.
- Lean: 90 module filenames with the same pattern in sibling `dashi_lean4`.
- Agda concentration: 3,003 in `DASHI/Physics`; the remainder spans Moonshine,
  Culture, Papers, Education, Biology, Cognition, Analysis, Governance, and
  other domains.
- Lean concentration: 68 in `NSBControl`, 14 in `Integration`, with smaller
  RequestProject/Dashi/Imported clusters.

## Migration order

1. Wilson Yang–Mills pilot (completed in commit `edf74db0c3`).
2. Bounded non-YM families with a stable semantic replacement, beginning with
   a reviewed Moonshine/Monster family and then Lean mirrors.
3. Large Physics families, only after owner-by-owner collision review.
4. Culture/Education and other programme archives, where the round may be a
   source or acquisition sequence and therefore needs an explicit semantic
   owner name rather than number stripping.

Mappings belong in `config/semantic-name-registry.json`. Generated/vendor/
archive/provenance paths remain excluded from active-name enforcement, while
historical numbers remain recoverable through registry and archive docs.

## Immediate collision risks

Base369/Monster3B representation bidi-search spans a long numbered chain, while
Culture and Education contain long acquisition/progress sequences. These cannot
safely be renamed by deleting digits: the number expresses ordering or source
checkpoint, and several target names would collide. Each family needs a curated
semantic vocabulary and an explicit registry batch.
