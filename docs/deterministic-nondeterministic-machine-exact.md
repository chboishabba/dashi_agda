# Deterministic and nondeterministic machine semantics

`DASHI/Mathematics/Complexity/DeterministicNondeterministicMachineExact.agda` adds the machine layer beneath the existing language/verifier/reduction formalisation.

A deterministic machine has:

```text
input carrier,
configuration carrier,
initial configuration,
partial next-configuration function,
accepting predicate.
```

`iterateDeterministic` executes an exact number of steps, returning `nothing` when the transition becomes undefined. Bounded acceptance carries an actual proof that the chosen number of steps is at most the supplied bound.

A nondeterministic machine replaces the partial next function by a finite successor list. `NDReach` is an inductive exact-step reachability relation.

Every deterministic machine is embedded by replacing

```text
next(c)=nothing
```

with an empty successor list, and

```text
next(c)=just c'
```

with the singleton list `[c']`.

The module proves:

```text
deterministic run of n steps
=> nondeterministic reachability in n steps,
```

and consequently:

```text
bounded deterministic acceptance
=> bounded nondeterministic acceptance
```

with the same input, step count, final configuration and bound witness.

Polynomial clocks, tape encodings, accepting-branch/certificate equivalence, universal simulation and Cook–Levin tableau size remain explicit boundaries. The module is rooted in the cumulative validation surface and guarded by the whole-repository checker.
