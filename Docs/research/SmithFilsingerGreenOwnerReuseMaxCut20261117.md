# Smith/Filsinger F02/F13 Green-owner reuse max-cut — 17 November 2026

## Source audit: the repository ALREADY has Green, but which one?

**Reused exact owners** (imported; none edited):
1. `DASHI/Physics/YangMills/BalabanFiniteCoerciveGreen.agda`: `CoerciveFiniteOperator`, `FiniteCoerciveInverseAuthority`, actual inverse `Green.inverse` with left/right inversion and reciprocal-coercivity norm bound; `toGreenOperatorBound`. A finite static inverse is NOT a hyperbolic Maxwell retarded kernel.
2. `DASHI/Physics/YangMills/BalabanSide4ScalarGreenConvolutionExact.agda`: actual `scalarGreen` exact finite 4D **periodic scalar elliptic** convolution and `siteGreenLaplacianIdentity`, with mean-zero correction. Its spatial convolution is nonlocal; it has no time axis or realistic soil/ionospheric boundary.
3. `DASHI/Physics/Motors/SmithFilsingerTimeIndexedTransferExact.agda`: existing `RetardedFlight`, with `launch + flight = arrival`.
4. `SmithFilsingerYeeCFLConeGuardExact.agda`: CFL ≠ proven physical light-cone front; explicit `CalibratedPhysicalCone` plus sourced distance/speed needed.
5. `SmithFilsingerSourceMaxwellBoundaryWeldExact.agda` and `SmithFilsingerMidpointPhaseWorkExact.agda`: original selected Smith/Filsinger configuration, signed natural/controller incident/outgoing, calibrated work and source-first ledger.
6. `SmithFilsingerSpaceTimePoyntingTelescopeExact.agda`, `SmithFilsingerIndexedSignedCellStokesExact.agda`: independently retained Maxwell energy/mesh proof owners.

**Other Green owners found but NOT falsely welded:** `BalabanClayT3PeriodicTorusGreenCarrierExact`, `BalabanGreenKernelDecayFinite` and `BalabanPeriodicBulkHessianGreenClosure` contain finite gauge-Hessian/Fourier/Combes–Thomas coercivity or **elliptic** decay. These are not the required source-driven stratified Maxwell–Hall–Pedersen dyadic Green; spatial exponential decay does not prove time-causal support. `KSW668BulkScalarReceiverRationalSliceExact` is a brane/gravity context and cannot be imported as physical Filsinger electromagnetic data without a separately licensed type map.

## F02/F13 results implemented on PR #1524

### A. Existing abstract finite inverse and norm control with exact time delay

New `SmithFilsingerCoerciveGreenRetardedWeldExact.agda` consumes the original Balaban finite coercive inverse and its reciprocal-coercivity norm bound. `retardedGreen` is an explicit total recursive function. `greenCannotRespondBeforeChosenDelay` proves response exactly equals the supplied zero vector at all times with a **strict, inductively witnessed** `StrictEarlier time delay`. `greenAtArrivalReadsExactlyLaunchedSource` proves the first arrival is `inverse(source zero)`; `greenAtArrivalInheritsCoerciveBound` imports the actual original Green norm certificate.

**Important launch-clock correction:** original `RetardedFlight` has BOTH launch time and flight duration, not merely a delay from global time zero. `stampedGreen` is shifted by the launch index. `stampedGreenIsTotalRetardedDelay`, `stampedGreenAtActualArrival` and `stampedGreenIsZeroBeforeActualArrival` prove absolute-clock consistency at `launch+flight`. Without this, nonzero original launch times can be mistaken for measured early receiver responses.

### B. Real selected-original physical identities, no empty-token evidence promotion

`OriginalSelectedRetardedGreen` is indexed by the SAME `SelectedBoundary b` and `FormalFieldToPort b`. It includes a concrete measured source vector and `sourceHistory zero = originalMeasuredSourceAtLaunch`; a concrete original physical Maxwell response operator and an explicit for-all-input equality to the admitted Green inverse; a concrete original source-to-collector distance, speed, and a `CalibratedPhysicalCone` certificate for that exact original flight; a zero-to-zero calibrated terminal-work sensor; exact sensor-at-arrival equals original useful load; and `naturalIncident = naturalOutgoing + independentlyMeasuredNaturalNetWork` for the SAME original port.

These are intentionally **still admitted physical measurements/identifications**, NOT constructed from the Green inverse. From them, the module derives `selectedOriginalGreenAtPhysicalArrival`, `selectedRetardedNoUsefulBeforeArrival` (relative launch local-clock version), `selectedGreenArrivalMatchesPhysicalMaxwellResponse` and `selectedPhysicalFrontDistanceBound`. Zero time-response is derived from the chosen delay, not from the static spatial inverse itself.

### C. Concrete exact periodic scalar Green delayed readback

New `SmithFilsingerPeriodicGreenDelayReuseExact.agda` imports the **actual** side-four torus `scalarGreen` convolution and original `siteGreenLaplacianIdentity`. `periodicDelayedGreen` stages its response by a natural-number delay; `periodicGreenBeforeLaunchIsZero` and `periodicGreenAtArrival` are derived by induction; `delayedPeriodicGreenSolvesMeanCorrectedLaplacian` transports the *original precise* identity

[
\Delta_h (G f)(x)=f(x)-\frac{1}{256}\sum_y f(y)
]

to delayed arrival. This is the **existing** elliptic kernel, with its genuine constant-mode subtraction, NOT a fictitious inverse without a nullspace. Using the correct mean correction matters.

## Independent exact arithmetic replay

Committed new `scripts/test_smith_filsinger_coercive_green_retarded_weld_exact.py` (source-equivalent numerical test using a positive-definite diagonal 2×2 rational operator). Independently replayed **327 exact Fraction checks PASS** for launch delays 0/1/4/9, flight times 0/1/3/7, strict pre-arrival no-response, Green inverse at the first actual arrival, exact inverse-left restoration, norm contraction by 1/2 in this diagonal example, and the zero-source/no-original-measurement controls. Source test included in existing combined Python runner.

Both new Agda sources included in the existing pinned `scripts/check_smith_filsinger_formal_weld_agda29.sh`. **No Agda 2.9/Nix executable here**, no latest-head full combined pytest run and no kernel-checked Green weld receipt. Original physical F02/F10/F13/F15 and D1 gates remain OPEN.

## Next max-cut after this verified-source reuse

1. **D1:** execute pinned Agda 2.9 for exact current PR #1524 head; repair whatever compiler actually reports, without promoting a source-only candidate.
2. **F02:** construct a **genuine 3D hyperbolic Maxwell retarded dyadic Green**, with sourced causal support and dispersive Hall/Pedersen/neutral-wind medium, not merely adding a delay to the static inverse.
3. **F13:** configure layered open soil/air/ionosphere boundary and the actual collector/ground terminal readout, with displacement current, contour integration and nonlinear source backaction; couple to real 3D Green surface response and the signed indexed Poynting ledger.
4. **F15:** independently metered natural net work over restored repeated cycles with all bridge, ionization, material/thermal and controller input; test any 100× ratio only after physical source identification.
5. **F16:** atmospheric rain/cooling causal branch remains downstream of proven physical energy transfer.

**Provenance:** Green and finite-coercivity operators are existing Yang–Mills/constructive DASHI owners; Smith/Filsinger direct nonlinear Sun–Earth coupling is the user-origin hypothesis; temporal-source composition is a new derived mathematical consumer. No ESD edits. An elliptic mathematical Green operator plus a stipulated delay is NOT a physically derived causal solar-energy Maxwell Green function.


## Final clock and admission strengthening

`selectedOriginalNoUsefulBeforePhysicalArrival` now proves a **zero same-original calibrated sensor readback** for any global time strictly earlier than `RetardedFlight.arrival`, using the genuine original `launch+flight=arrival` proof to transport the bound. This closes a source-level clock-index loophole that a delay-only operator would otherwise leave open. The inference depends on the explicit calibrated `sensorZero` field, not on a claim that static elliptic Green support has finite physical speed.

`selectedGreenArrivalMatchesPhysicalMaxwellResponse` additionally transports the independently supplied `physicalMaxwellGreenMatchesChosenInverse` for the same measured launch vector, and `selectedPhysicalFrontDistanceBound` consumes `CalibratedPhysicalCone` on the same selected flight. These are valuable *typed proof obligations*, not a measured or solved physical operator. Any chosen source data or a trivial physically false speed bound would fail the intended **empirical** qualification even if an abstract Agda record were inhabited.
