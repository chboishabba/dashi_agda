# NS Round 32 — indexed gluing and bounded resource transport

This tranche formalises the architectural lesson from the fibre/indexing work without claiming a new Navier–Stokes estimate.

## Same-object indexed gluing

An external coordinate presentation may be consumed only after an explicit equality identifies its transported representative with the literal physical carrier. The encoding is therefore transport across an indexed seam, not replacement by an extensionally similar object.

## Product resource lattice

Every `AdmissibleRemainder` compiles to four coordinates:

1. dissipation fraction;
2. data/lower-order resource;
3. known critical-integral coefficient;
4. forbidden continuation resource.

The fourth coordinate is proved identically zero by structural recursion. `OwnerDerivation` has constructors only for the existing admissible grammar, so derivations cannot cross into BKM, Serrin, or target-critical-supremum dependencies.

## Inverse-scale transport

`InverseScaleTransport` packages a Round-31 `HHBadTimeScaleCell` together with the statement that the source and target differ by exactly one shell power. Its consumer is the existing exact theorem

```text
activeTime * lambda <= eta * nu
  => activeTime * lambda^3 * E <= eta * nu * lambda^2 * E.
```

The physical producer remains explicitly false. This round does not prove the physical HH-bad producer.

## Nine-owner carrier

The nine owners are given a duplicate-free 3 x 3 bookkeeping carrier. This is organisational, not a claim of a new square symmetry of Navier–Stokes. Only the literal `LH <-> HL` transpose is recorded as an involution.

## Rule enforced

Never transport a bound without transporting its index, carrier, background, and resource valuation.
