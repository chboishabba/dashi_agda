# Bc*+ / Bc+ Shell Prediction Ladder

This note documents the local Agda receipt in
`DASHI/Physics/Closure/BcStarShellPredictionLadder.agda`.

The receipt is intentionally narrow. It fixes the carrier to `(c, anti-b)`,
labels the ground shell as `Bc+` pseudoscalar and the excited shell as `Bc*+`
vector, and computes a toy natural-number energy ladder:

- ground toy energy: `6325`
- excited toy energy: `6367`
- predicted delta: `42`

The parameter packet is frozen before empirical comparison. The receipt also
records `empiricalDataInspected = false`, blocks any local empirical-comparison
receipt, and keeps promotion false.

It does not claim a calibrated physical mass, QCD potential, dataset match,
or empirical promotion.
