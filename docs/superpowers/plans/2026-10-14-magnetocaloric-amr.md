# Magnetocaloric AMR Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Add a reusable, source-bounded formalisation of magnetocaloric active-regenerator cooling with materials integrity and work-recovery contracts.

**Architecture:** Build focused Agda modules for material response, regenerator transport, AMR cycle semantics, protected-system closure, and a MAGNOTHERM source-boundary receipt. Keep calibrated constitutive values and vendor performance claims outside theorem authority.

**Tech Stack:** Agda; existing DASHI thermodynamic law records; repository proof-receipt/source-boundary conventions.

**Spec:** `docs/superpowers/specs/2026-10-14-magnetocaloric-amr-design.md`

## Global Constraints

- MAGNOTHERM is a parameterised evidence witness, not the generic abstraction.
- Maxwell and adiabatic response relations are explicit predicates/evidence fields, not universal axioms.
- Constitutive coefficients and device performance require calibration.
- Work recovery cannot exceed declared recoverable work.
- External vendor claims remain source observations, not proved performance theorems.

## Review Focus

- Sign/convention neutrality for magnetic heat/entropy response.
- No accidental proof of positive cooling merely from cycle construction.
- Periodic steady state remains an explicit witness.
- Degradation contracts distinguish qualified interval from indefinite lifetime.
- Source-boundary records distinguish peer-reviewed observations from vendor claims.

---

### Task 1: Material response core
Create `DASHI/Physics/Thermodynamics/MagnetocaloricMaterial.agda`; expose material state, response maps, Maxwell/adiabatic evidence predicates, calibration gate, and authority boundary.

### Task 2: Caloric regenerator transport
Create `DASHI/Physics/Thermodynamics/CaloricRegenerator.agda`; expose porous geometry, solid/fluid transport, reversible-flow orientation, conservation and hydraulic admissibility.

### Task 3: AMR cycle semantics
Create `DASHI/Physics/Thermodynamics/ActiveMagneticRegenerator.agda`; expose four phases, phase operators, cycle composition, synchronisation, periodic steady-state and explicit cooling witnesses.

### Task 4: Protected-system closure
Create `DASHI/Physics/Thermodynamics/ProtectedMagnetocaloricSystem.agda`; expose degradation/protection, safe-envelope qualification, work recovery, first/second-law accounting and validity composition.

### Task 5: MAGNOTHERM source boundary
Create `DASHI/Physics/Thermodynamics/MagnothermSourceBoundary.agda`; encode sourced observations, provenance class, and explicit non-promotion of vendor claims.

### Task 6: Integration and audit
Create `DASHI/Physics/Thermodynamics/Everything.agda`; add a compile-consumer `DASHI/Physics/Thermodynamics/MagnetocaloricAMRReceipt.agda` that instantiates the dependency chain at type level and owns the remaining-calibration frontier.
