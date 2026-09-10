# Gödel concrete diagonal current cut

This tranche narrows the diagonal-lemma lane without claiming Gödel I/II or universal undecidability closure.

## Source-written concrete substrate

- raw de Bruijn first-order arithmetic syntax;
- capture-avoiding substitution/instantiation;
- exact prefix token serialization;
- base-12 token-stream arithmetic with 0 terminator and digits 1..11;
- total well-founded Nat decoder;
- source-level `decode(encode formula) = formula` retraction.

## Generic compilers already owned

- formula-code retraction -> arithmetised substitution;
- represented self-substitution -> diagonal construction;
- primitive-recursive self-substitution + representability + object-language precomposition -> diagonal lemma.

## Live theorem-bearing coordinates

1. exact source alignment/certification of primitive-recursive representability and the object-language closure used by the diagonal construction;
2. for the custom executable base-12 code, a same-code proof that the concrete self-substitution function is primitive recursive.

The historical/source-native Gödel numbering and the executable base-12 presentation remain distinct. A theorem about one does not transport to the other without an explicit same-code or semantics-preserving weld.

## Validation boundary

Source-written does not mean Agda-kernel certified. The validation root imports the complete tranche, but exact-head workflow status must be checked independently before any certification claim.
