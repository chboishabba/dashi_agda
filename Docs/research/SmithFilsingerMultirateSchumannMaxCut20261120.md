# Filsinger multirate source discriminator — 2026-11-20

User hypothesis: near 1000:1 carrier/Schumann relationship. Existing FilsingerLydenEarthPortMaxCut20261110 documents 7800 Hz acoustic / 7.83 Hz nominal = 996.17, not proven electrical frequency, intentional harmonic tuning or ELF phase lock. Nominal 1000th multiple 7830 Hz differs by 30 Hz. Prior acoustic 2:1 phase test is separate.

Reuse check_smith_filsinger_dispersive_finite_line.py nonlinear polarization and signed material work. New standalone SymPy discriminator verifies quadratic mixed Laurent coefficients, pure-fast polynomial absence of slow subharmonic through tested degree 8, exact nonlinear material energy differentiation, nominal detuning and travelling phase difference identity. All 15 assertions passed locally. No CI or Agda execution. All-degree pure-tone result follows by Laurent support closure under multiplication; finite tests alone do not prove kernel theorem.

Do not identify period-two switching with 1000:1 frequency ratio. Next: sparse independent fast/slow harmonic indices, source-calibrated memory and propagation, same-object measured electrical and acoustic clock, separate source/driver/modulation work. No atmospheric intervention design, actual circuit topology, harvesting or Schumann excitation claimed.
