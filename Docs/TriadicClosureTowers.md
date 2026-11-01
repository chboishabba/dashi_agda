# Triadic closure towers

This note separates three constructions that had been conflated in informal discussion.

## 1. Cartesian triadic axes

A three-axis carrier such as Self/Mirror/Norm is a Cartesian product of three trits.
It has `3 * 3 * 3 = 27` states.  In the Agda module this is `TriadicCube = Trit -> Trit`.

This is not a power tower.

## 2. Function-space power towers

A genuine power tower appears when the next carrier is the set of all ternary-valued
functions on the previous carrier:

- bottom carrier: `Trit`, cardinality 3;
- first function layer: `Trit -> Trit`, cardinality `3^3 = 27`;
- second function layer: `(Trit -> Trit) -> Trit`, cardinality `3^(3^3)`;
- and so on.

Accordingly, `ThreeTowerCarrier 2` is the precise type-level reading of
"three-super-three-super-three".  Its cardinality is

`3^(3^3) = 3^27 = 7,625,597,484,987`.

The same recurrence over a nine-element carrier gives `NineTowerCarrier`.
`NineClosureHeightEight = NineTowerCarrier 7` denotes eight stacked 9s:

`9^(9^(9^(9^(9^(9^(9^9)))))))`.

It is not enumerated.  Even the three-high tower `9^(9^9)` already has
369,693,100 decimal digits.  The eight-high tower has approximately
`0.9542425094 * (the seven-high tower)` decimal digits.  The digit count is itself
an incomprehensibly large power tower.

This is a finite integer for every fixed height; it is not automatically a surreal
number or a transfinite object.  Surreal/cut structure would require an additional
recursive order or admissibility construction, not size alone.

## 3. M3, M6, and M9 roles

The module keeps the roles distinct:

- `M3 A = A`: an object or stance;
- `M6Arrow A`: an unsublated directed opposition between two `A` objects;
- `M9Closure A`: that opposition together with a chosen synthesis object.

M6 is therefore not a terminal prohibition and not itself the completed M9 object.
It is the arrow that must be traversed by supplying a synthesis.  `promoteSix`
constructs the corresponding M9 closure.

At the next order:

- `SixOfNine A = M6Arrow (M9Closure A)` is an opposition between two already
  closed worlds;
- `NineOfNine A = M9Closure (M9Closure A)` closes that higher-order opposition;
- `ThreeOfNine A = Trit -> M9Closure A` is a minimum triadic axis whose positions
  are themselves closed worlds.

This makes "6 of 9" precise without identifying 6 with closure, and it allows the
same object/arrow/closure rhythm to recur at higher orders.

## Claim boundary

The module proves only the finite carrier recurrence and the typed M3/M6/M9
construction.  It does not claim that large cardinality alone yields cognition,
profitability, physical dimension, topology, surreal numbers, or a universal
closure theorem.
