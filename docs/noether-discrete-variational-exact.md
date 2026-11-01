# Exact discrete Noether transport

`DASHI/Mathematics/Symmetry/NoetherDiscreteVariationalExact.agda` closes the algebraic conservation step that was previously only represented downstream by a defect ledger.

For one discrete variational step, write the contracted discrete Euler–Lagrange identity as

```text
incomingMomentum + firstVariation = eulerResidual
```

and the contracted infinitesimal symmetry identity as

```text
firstVariation + outgoingMomentum = symmetryResidual.
```

The module eliminates the shared first-variation term and proves exactly over the rationals that

```text
outgoingMomentum - incomingMomentum
  = symmetryResidual - eulerResidual.
```

Consequently, when both residuals vanish,

```text
incomingMomentum = outgoingMomentum.
```

The residual theorem is converted directly into the existing `NoetherDissipationDefectExact.DefectLedger` with zero dissipation and residual equal to the difference between the symmetry and Euler–Lagrange defects.

This is a checked Noether cancellation theorem rather than a theorem-name placeholder. The geometric and differential input remains explicit: a separate instantiation record must supply a configuration carrier, symmetry generator, discrete Lagrangian data, slot derivatives, momentum-map data and a contracted step satisfying the two displayed identities.

Sources recorded in the Agda header:

- Emmy Noether, *Invariante Variationsprobleme* (1918); original publication has no assigned DOI. M. A. Tavel translation, *Invariant Variation Problems*, DOI `10.48550/arXiv.physics/0503066`;
- J. E. Marsden and M. West, *Discrete mechanics and variational integrators*, DOI `10.1017/S096249290100006X`.

The module is imported by the cumulative cross-pollination root and named explicitly in the no-hole/source/scope checker. The final validation target remains the whole-repository wrapper `DASHI.EverythingHurwitzHopfNoetherCrossPollination`.
