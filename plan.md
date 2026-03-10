# Dashboard Plan

1. **Dynamics law lock** – already exported via `CanonicalDynamicsLawTheorem` and
   wired all the way through Stage C; no further code edits needed here unless
   deeper proofs appear.
2. **Known-limits scaffolding** – local causal propagation/coherence modules exist;
   verify the documentation and summary exports mention them explicitly.
3. **Bridge completion** – build the missing theorem-backed full gauge/matter
   recovery and upgrade the GR/QFT bridge theorems accordingly.
4. **Validation and release** – run `agda -i .` across the touched modules,
   update `PhysicsClosureValidationSummary.agda`, and ensure the orchestrator
   marks `milestones_remaining` as 0 once the bridge suite ships.
