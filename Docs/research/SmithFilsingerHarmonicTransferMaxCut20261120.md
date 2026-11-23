# Finite harmonic transfer and quadrature work (2026-11-20)

Extends SmithFilsingerSwitchedADEFloquetMaxCut20261120 using the original
switched ADE transition and floquet functions. For primitive Nth root r,
each input harmonic column uses multiplier lambda*r^n and the original
monodromy resolvent. Output envelope DFT produces the finite N-block
state response matrix. Harmonics are modulo N; not a flux-normalized
physical scattering matrix or infinite continuous Fourier series.

Complex work is the sum of the original real midpoint ledger evaluated
on real and imaginary quadratures. It is not automatically single-real
cycle work. For unit-modulus lambda, endpoint quasi-periodicity implies
quadrature storage return over one modulation period. Tests cover N=2,3,4,
one cell, fixed and alternating permittivity, mixed complex harmonic input;
stationary off-diagonal zero, switched nonzero off-diagonal witness,
direct equation reconstruction, nonnegative dissipation and work closure.
Complex expression comparison requires algebraic simplification.

Fresh local execution: 86 new counted assertions, plus 288 switched ADE
and 57 two-phase Floquet checks = 431 counted checks. Prior two producer
blobs match GitHub; stationary donor is reconstructed locally. No CI or
Agda execution. General N constructor accepts only roots whose required
identities SymPy resolves; acceptance tested only N=2,3,4.

Next: exact committed source replay with original donor; multi-cell and
multi-input harmonic regression; real physical observation and power-flux
normalization; Bishop Fourier bridge; 2023/2025 optical raw data; original
ZVS source/clock/port metrology; KK/YM/TSVF same-object attachment.
No original device harvesting, spatial light cone or physical KK claim.
