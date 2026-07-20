# DNA chemistry sheet cross-pollination

## Productive synthesis

The DNA formalism already contained several individually useful lanes. The productive integration is a typed sequence of representations rather than one object being renamed to cover them all:

```text
raw DNA
  -> exact U/V coordinates
  -> chemistry-visible feature map / quotient
  -> signed chemistry-coordinate image
  -> local and aggregate chemistry energies
  -> future coefficient sheets
  -> future expanded detail fields
  -> optional ternary quantisation
  -> optional phase/eigenspace representation
  -> rendering and diagnostics
```

`Ontology.DNA.ChemistrySheetCrossPollination` records this spine and the authority boundary between its stages.

## Exact joins available now

### Raw DNA and U/V

`ChemistryUVCoordinates` is an exact coordinate chart:

- encoding followed by decoding reconstructs the original sequence;
- the U/V pair determines every base;
- admissibility predicates can be pulled back through the decoder.

This is not yet a chemistry quotient by itself. It is an exact change of coordinates.

### U/V and the chemistry feature map

The concrete chemistry feature map agrees definitionally with the feature extracted through the U/V bridge. The quotient lane can therefore consume the exact coordinate chart without duplicating base classification.

### U/V and signed chemistry energy

The existing signed `SheetCoordinates` can be obtained by decoding an exact U/V packet and applying the signed chemistry map. This gives a clean bridge into the current transition/coupling Hamiltonian.

The signed image is best treated as a quantised chemistry-coordinate image, not as proof of a multiscale sheet decomposition.

## Reusable ideas from the wider DASHI formalism

### Quotients

The chemistry equivalence relation belongs at the feature or assay-observable layer. Exact U/V coordinates should remain below it so that a downstream quotient can decide which distinctions are chemically operational rather than losing them prematurely.

### Hamiltonians and MDL/action

Chemistry energies can rank or screen representatives within a quotient class. This does not imply that every chemistry observable is quadratic, that energy equals MDL, or that every energy component is monotone under an encoder update.

A later codec can combine hard admissibility, incremental chemistry energy, multiscale energy once a real tower exists, description length, checksum cost, and channel-recovery cost. Those terms should remain separately named before a combined action is promoted.

### Involution and reverse complement

Complement and reverse-complement actions should commute with promoted analysis and expansion maps where claimed. This is the correct cross-pollination point for the existing involution formalism: a typed equivariance obligation at each level.

### Ternary

Balanced ternary is a plausible quantisation of signed coefficients only after a quantiser is supplied. Promotion requires thresholds or a state-dependent partition, a representative/reconstruction map, and a chemistry-feature or energy distortion bound.

Positive, negative, and small-looking heatmap values alone do not establish that theorem.

### Phase and eigenclasses

A phase/eigenspace reading requires an operator, its action, and a relation between eigenspaces and chemistry-equivalence classes or low-energy basins. Phase is downstream of that operator theorem rather than a synonym for signed ternary values.

### Tetrational sheets

The fixed `4 -> 16 -> 64 -> 256` carrier can serve as one finite instance or truncation of a broader recursive construction. Connecting it to tetration requires a recursive level constructor, explicit composition semantics, an embedding of the finite DNA carrier, reconstruction, and transport of chemistry observables.

## Current non-promotions

The integrated surface records:

- exact U/V feeds the quotient: yes;
- exact U/V feeds the signed-energy lane: yes;
- signed chemistry coordinates are already detail sheets: no;
- fixed carrier nesting determines tetration: no;
- ternary quantisation needs an error bound: yes;
- phase eigenspaces need an operator: yes;
- all chemistry terms are necessarily quadratic: no.

## Next implementation target

The highest-value next step is an equivariant tower instance, not another heatmap:

1. instantiate a real level-indexed analysis/expansion/reconstruction tower;
2. prove complement and reverse-complement equivariance;
3. transport selected chemistry observables to levels without claiming all chemistry is band-local;
4. add a ternary quantiser with a chemistry-energy distortion bound;
5. only then add the phase/eigenclass representation for the resulting operator.
