# Magnetocaloric AMR Formalisation Design

## Purpose

Introduce a reusable formal lane for magnetocaloric cooling systems, with MAGNOTHERM as an externally sourced witness rather than a company-specific special case. The lane composes the existing thermodynamic/state-law abstractions with magnetic material response, active magnetic regeneration, transport, cyclic control, work recovery, and materials-integrity degradation.

## Architecture

The formal ladder is:

1. `MagnetocaloricMaterial` — material-law surface relating temperature, field, magnetisation, entropy, heat capacity, and admissible regime.
2. `CaloricRegenerator` — porous solid/fluid regenerator with coupled transport and hydraulic admissibility.
3. `AMRCycle` — four-phase operator cycle (`magnetise`, `hotBlow`, `demagnetise`, `coldBlow`) with synchronisation and periodic-state contracts.
4. `ProtectedAMRSystem` — closure adding degradation state, protection strategy, safe operating envelope, work recovery, first/second-law cycle accounting, and conservative promotion boundaries.

MAGNOTHERM-specific facts live in a source-boundary module as evidence-backed observations. Vendor performance claims remain explicitly observational rather than promoted theorem authority.

## Correctness contracts

A valid magnetocaloric cooling system requires material-law admissibility; magnetocaloric compatibility; transport conservation and hydraulic admissibility; cycle synchronisation and periodicity; positive extracted cooling as an explicit witness; first-law cycle accounting; nonnegative entropy production; qualified material integrity; and bounded work recovery.

## Authority boundary

This formalisation does not prove commercial COP, lifetime, capacity, or vendor efficiency claims. Promotion to calibrated performance requires same-device measurement and explicit constitutive/calibration evidence.
