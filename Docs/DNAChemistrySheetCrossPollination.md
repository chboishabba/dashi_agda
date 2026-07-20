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

The signed image is coarser than the exact U/V carrier because `Signed` includes a zero state and the current producer emits only positive and negative values. It is therefore best treated as a quantised chemistry-coordinate image, not as proof of a multiscale sheet decomposition.

## Reusable ideas from the wider DASHI formalism

### Quotients

The chemistry equivalence relation belongs at the feature or assay-observable layer. Exact U/V coordinates should remain below it so that a downstream quotient can decide which distinctions are chemically operational rather than losing them prematurely.

### Hamiltonians and MDL/action

Chemistry energies can rank or screen representatives within a quotient class. This does not imply that every chemistry observable is quadratic, that energy equals MDL, or that every energy component is monotone under an encoder update.

A later codec can combine:

- hard admissibility predicates;
- local incremental energy;
- multiscale energy when a real tower exists;
- description length or payload cost;
- checksum and channel-recovery costs.

Those terms should remain separately named before any combined action is proved useful.

### Involution and reverse complement

Complement and reverse-complement actions should commute with any promoted analysis/expansion maps where claimed. This is the correct cross-pollination point for the existing involution formalism: not “every sheet is symmetric,” but a typed equivariance obligation for each level.

### Ternary

Balanced ternary is a plausible quantisation of signed coefficients only after a quantiser is supplied. Promotion requires at least:

- thresholds or a state-dependent partition;
- a reconstruction or representative map;
- an energy/feature distortion bound;
- a statement of whether zero means inactivity, tolerance, cancellation, or an exact neutral state.

The existence of positive, negative, and small-looking heatmap values does not establish those facts.

### Phase and eigenclasses

A phase/eigenspace reading requires an operator, its action, and a relation between its eigenspaces and chemistry equivalence classes or low-energy basins. Phase language can then be useful for coherent/incoherent components, but it is downstream of the operator theorem rather than a synonym for signed ternary values.

### Tetrational sheets

The fixed `4 -> 16 -> 64 -> 256` carrier can serve as one finite instance or truncation of a broader recursive construction. To connect it to tetration, a future module must specify:

- the recursive level constructor;
- what is exponentiated or composed;
- the embedding of the finite DNA carrier into that tower;
- analysis and reconstruction across the embedding;
- how chemistry observables transport along it.

This preserves the user's intended tetrational formalism without falsely identifying ordinary block lengths with tetration.

## Current non-promotions

The integrated surface explicitly records:

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
