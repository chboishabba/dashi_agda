# NS Commutator Equivalence

Sprint 5 confirms the NS obstruction did not move.

The HighLow term has been reduced to the commutator form, but the remaining
control is equivalent in strength to low-mode Lipschitz control:

```text
CommutatorLipschitzControl
  <=> control ||grad u_<K||_LInfinity
  <=> no finite-time blowup control needed for Clay NS
```

The following attempted routes are recorded as circular for Clay use:

```text
Bernstein
enstrophy
Besov
```

The earlier `K^(-1/2)` suppression claim remains retracted.  HighLow control
is not accepted, and Clay Navier-Stokes remains false.

