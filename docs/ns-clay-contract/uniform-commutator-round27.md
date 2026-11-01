# Round 27 — cutoff-independent finite commutator coefficient

Round 26 separated the exact finite-kernel commutator identity from the finite first-moment scale law. Round 27 composes those two pieces in the critical low-advection tax.

For one dyadic cell, the kernel moment contributes an inverse scale and the differentiated high-frequency factor contributes the direct scale:

```text
shell moment        = 2^(-q) mother moment
shell high gradient = 2^q mother high gradient.
```

The carrier requires the exact inverse law

```text
2^(-q) * 2^q = 1.
```

The complete shell cell tax therefore reduces exactly to the mother-cell tax. The proof is recursive over arbitrary finite cell lists, so the coefficient contains no shell cutoff.

Concrete witnesses are checked for the scale pairs

```text
1 and 1,
1/2 and 2,
1/4 and 4.
```

This closes the finite scale-cancellation part of the low-advection commutator package. It does not yet prove the continuum periodic operator estimate, the physical time-dependent shell balance, or a strict total viscosity margin.

The second module connects the finite Galerkin energy identity directly to the bounded-energy hypothesis consumed by a continuation theorem. The slack is the accumulated nonnegative dissipation itself; no independent boundedness receipt is accepted. A repository-real Picard–Lindelöf instance remains open.

## Sources

- Jean-Michel Bony, *Calcul symbolique et propagation des singularités pour les équations aux dérivées partielles non linéaires*, DOI `10.24033/asens.1404`.
- Hajer Bahouri, Jean-Yves Chemin and Raphaël Danchin, *Fourier Analysis and Nonlinear Partial Differential Equations*, DOI `10.1007/978-3-642-16830-7`.
- Xiaoyutao Luo, *A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization*, DOI `10.1007/s00021-019-0411-z`.
- Jean Leray, *Sur le mouvement d'un liquide visqueux emplissant l'espace*, DOI `10.1007/BF02547354`.
- Roger Temam, *Navier–Stokes Equations: Theory and Numerical Analysis*, DOI `10.1090/chel/343`.

## Validation

```bash
bash scripts/check_ns_luo_uniform_commutator_round27.sh
```

No Agda-kernel or Actions success is asserted until observed.
