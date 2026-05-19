# Physics Archive Coverage Map

This note records the current archive-backed coverage map for the remaining
physics-closure work. It is intentionally narrower than “all Agda-adjacent
threads in the DB”; the point is to identify which archived discussions
actually reduce the current theorem risk in this repo.

## Scope boundary

The local DB sweep is broad enough to drive prioritization and lane assignment.
It is not a claim that every historical Agda/formalism thread has been fully
audited.

## Canonical archive anchors

### 1. Physics Closure in DASHI

- Online UUID:
  `69a80d0b-28b4-839b-aaae-90f7d7f0589c`
- Canonical thread:
  `2fa5dc5c445be6ce34c31cf6d2d9f94c6d029320`
- Source:
  local DB

Why it matters:

- highest-signal thread for the still-open closure spine;
- dense in RG, cone, delta, projection, Lorentz, gauge, and continuum terms;
- confirms that the bottleneck is theorem promotion and coupling of dynamics to
  invariants, not missing vocabulary.

Repo-facing use:

- primary archive support for:
  - derived dynamics law;
  - realization-independent projection/delta theorem;
  - continuum scaling law.
- also now records a sharper upstream research split:
  - finite-algebra / Morita / gauge-classification material is present in the
    thread, but it is downstream of the current closure bottlenecks;
  - the nearer-term actionable theorem pressure remains on projection/delta,
    Lorentz forcing, and continuum promotion.

### 2. Branch · Cone monotonicity analysis

- Online UUID:
  `699dc8f6-b6f0-839e-8b3a-7912abb07093`
- Canonical thread:
  `64ca6555941802f7cd4974541eab012188b635b3`
- Source:
  local DB

Why it matters:

- high-signal thread for cone, delta, projection, Lorentz, and quadratic
  structure;
- reinforces the current repo direction that the honest invariant is on
  projected deltas rather than absolute states;
- sharpens the boundary/interior reading of cone monotonicity instead of
  treating it as an all-or-nothing predicate.

Repo-facing use:

- direct support for:
  - projection/delta theorem promotion;
  - execution/delta interface refinement;
  - dynamics-law strengthening.
- additional recovered direction:
  - do not overclaim orthogonality from non-expansiveness alone;
  - the stronger mathematical route is closest-point / proximal structure or
    MDL-energy-first quadratic recovery.

### 3. Branch · Snap Filtering Analysis

- Online UUID:
  `69a392fb-aba0-8398-93b8-7951cc8297ac`
- Canonical thread:
  `0841ea838af3f2a00f66812316133e2162d9d550`
- Source:
  local DB

Why it matters:

- no longer just an operational analysis thread;
- high density in signature, cone, delta, projection, and collapse terms;
- includes explicit interface ideas such as arrow-separated delta cone and
  masked orthogonal split.

Repo-facing use:

- support lane for:
  - signature forcing;
  - execution-side delta interfaces;
  - collapse-vs-filter artifact separation.
- stronger extracted theorem guidance:
  - arrow-separated delta cone is the honest interface;
  - the arrow coordinate should orient forwardness but stay outside the
    quadratic itself;
  - masked orthogonal split remains a real candidate bridge after that
    separation, not before.

### 4. Branch · Topology and MDA/MDL

- Online UUID:
  `69718c29-6bcc-8324-b9e9-e412af8c89eb`
- Canonical thread:
  `53a59124cb8ef2f2e3a708a31fceb0010f3208ca`
- Source:
  local DB

Why it matters:

- strongest archive concentration for sparse operators, twist channels, phase,
  and MDL-side physical structure;
- useful for identifying what the current local formalism still lacks at the
  physical implementation layer.

Repo-facing use:

- support lane for:
  - continuum scaling law;
  - physical realization bridge;
  - missing twist/phase transport channels.

### 5. Branch · Visualising Collapse and Sparsity - RTX - light transport

- Online UUID:
  `69719a75-e538-8320-b5cc-1da13392b090`
- Canonical thread:
  `ea0e0d537a1c6effd17bba4c32faeec4f8fc66f5`
- Source:
  local DB

Why it matters:

- best current physical bridge outside the formal Agda layers;
- contains the strongest multi-sensor wavefield and phase-synchronization
  discussion;
- gives a real physical analogue for quotient observables and MDL-style
  representative selection.

Repo-facing use:

- support lane for:
  - physical reality bridge note/prototype;
  - possible future continuum interpretation work.

Current boundary:

- this thread has informed prioritization, but there is still no dedicated
  local theorem or prototype for the lensless / phase-synchronization bridge.
- the thread is strongest on multi-sensor wavefield reconstruction and phase
  synchronization; it is not currently evidence that the archive already
  contains a finished lensless time-of-flight formalism.

## Prioritization

### P0

- derived dynamics law;
- realization-independent projection/delta theorem;
- signature forcing and execution-side delta interface;
- continuum scaling law.

### P1

- physical reality bridge from wavefield reconstruction / phase
  synchronization.

### P2

- algebraic-carrier, root-system, modular, and moonshine-adjacent threads
  unless they directly help the P0 physics closure spine.

## Worker lanes

- Kepler:
  derived dynamics law
- Hegel:
  signature forcing / arrow-separated delta interface
- Confucius:
  realization-independent projection/delta theorem widening
- Pascal:
  continuum scaling law
- Tesla:
  physical reality bridge from wavefield / phase synchronization
- Parfit:
  advisory algebraic-carrier lane only

## Current conclusion

The archive now supports the current repo direction strongly enough that the
next step should be theorem-bearing work on the P0 lanes, not a wider search
for more analogies.
