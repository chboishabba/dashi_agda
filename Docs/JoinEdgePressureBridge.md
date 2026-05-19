## Join-Edge Pressure Bridge

This canonical note records the current thread connection between the ITIR/SensibLaw join lattice and the DASHI pressure/severity surfaces already formalized in this workspace.

- **Join lattice → pressure:** each representative edge (`MATCH`, `LEFT_ONLY`, `RIGHT_ONLY`, `CONFLICT`, `OVERRIDE`, `GAP`, `SUBSUMES`, `OVERLAP`, `UNRESOLVED`) expresses a pattern of constraint satisfaction, contradiction, or missing coverage; those patterns inflate the violation/pressure channel counted by `illegalCountP2` and bounded by `forcedStableCountOrbitP2`, see `Docs/HeckeRepresentationLayer.md#law-vs-reality-inference` and `Ontology/Hecke/DefectOrbitCollapseBridge.agda` for the concrete anchors.
- **Severity gate:** the severity lattice in `DASHI/Physics/SeverityGuard/Core.agda` plus its `SeverityPolicy` thresholds (`safeThreshold`, `brokenThreshold`) are the existing guard surfaces that now receive the join-derived pressure tuple (`I = illegalCountP2`, `F = forcedStableCountOrbitP2`) so `SG.Guard`/`SG.Broken` match the intended `guard/snap/broken` tiers coming from policy severity summaries.
- **UFTC lattice & Lyapunov:** the UFTC carrier (`UFTC_Lattice.agda`) is the ambient combinatorics for that severity join, and the Lyapunov/MDL machinery (`DASHI/MDL/MDLLyapunov.agda`, `DASHI/Physics/Closure/MDLLyapunovShiftInstance.agda`) ensures the coarse-step map respects the same descent order that the join test now expects (`MATCH` edges stay low-pressure while `CONFLICT`/`UNRESOLVED` edges feed the `Lyapunov`-monotone defect increase).

This minimal note keeps everything tightly referenced so the next canonical surface can cite these anchors rather than re-deriving them later.
