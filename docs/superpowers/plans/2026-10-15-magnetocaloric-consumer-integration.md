# Magnetocaloric Consumer Integration Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Populate all sound existing consumers of the magnetocaloric/AMR lane without introducing false physical equivalences.

**Architecture:** Add typed crosswalk modules at the SI, electromagnetism, condensed-matter, chemistry/atomic, quantum/statistical, continuum-law and magnetostructural boundaries. Keep the AMR device layer abstract and require evidence-bearing bridges from each lower layer.

**Tech Stack:** Agda, existing DASHI physics law and SI modules.

**Spec:** `docs/superpowers/specs/2026-10-15-magnetocaloric-consumer-integration-design.md`

## Global Constraints

- Reuse existing carriers before introducing new ones.
- Preserve source/authority boundaries and `shared carrier != shared observable` separation.
- Do not treat tesla (B) as magnetic field strength H; use A/m separately.
- Do not infer Clay NS or YM results from AMR engineering.
- No numerical material/device claim without calibration evidence.
- Keep BIPM-owned canonical `SI.agda` unchanged when a domain-specific derived dimension can live in the consumer.
- Preserve canonical DASHI attribution: author/title/publication/DOI/source kind/formalisation relationship; primaryness is claim-relative; access carrier != authorship/authority; citation != proof; vendor/planned evidence cannot pay independent same-device calibration.

## Review Focus

- B-vs-H dimensional confusion must be impossible at the SI type level.
- Same material state must not imply identical crystal, magnetic, electronic and thermodynamic observables.
- Atomic-shell stability must not imply magnetocaloric response without a material-identification bridge.
- A quantum Hamiltonian must not imply a calibrated partition/free-energy map without an ensemble witness.
- Continuum/NS reuse must stop at application-specific balance/transport interfaces and never promote Clay regularity.
- Source identity, access transport, source claim, DASHI reconstruction and theorem/device authority must remain separate.
- Cross-object family evidence and same-platform/different-material device evidence must not be promoted to exact LaFeSi same-object closure.

---

### Tasks 1-8: consumer and structural integration

- [x] SI/metrology consumer with B/H separation and traceability.
- [x] U(1) electromagnetic consumer with field-geometry/B-H/validation obligations.
- [x] Condensed-matter crystal/magnetic consumer with separate observable projections.
- [x] Atomic/protection chemistry consumer with composition/coating/fluid separation.
- [x] Quantum/statistical consumer with Hamiltonian -> ensemble -> free-energy evidence chain.
- [x] Continuum/NS boundary consumer without Clay regularity promotion.
- [x] Magnetostructural mechanics consumer with calibration-bound magnetostriction/fatigue.
- [x] Consumer atlas / terminal receipt / thermodynamics reachability.

### Task 9: Attribution firewall and same-study empirical payments

- [x] Replace thin local source abstraction with `DASHI.Core.AttributedSourceCore`.
- [x] Separate ACS/PMC/Aalto access carriers from authorship and authority.
- [x] Encode same-study in-device VACUUMSCHMELZE LaFeSi composition envelope.
- [x] Encode six-week aging, preliminary three-month microchannels, 1 T delta-T_ad function check and load-free ~288 K / 2 Hz / ~0.8 T operating point.
- [x] Keep months-to-years aging as future work.
- [x] Keep 30%, STELLAR 5 T, 125 kW+ and 250 kW+ statements vendor/development-only.

### Task 10: Cross-object La-Fe-(Mn)-Si-H family acquisition

- [x] Attribute Radulov et al. 2017, DOI `10.1016/j.actamat.2017.01.054`.
- [x] Pay family NaZn13 crystal/transition prior and magnetovolume/thermal-mechanical coupling without exact-material promotion.
- [x] Attribute Krautz et al. 2014, DOI `10.1016/j.jallcom.2014.02.015`.
- [x] Pay Mn/Si/hydrogenation response/stability prior without exact-batch promotion.
- [x] Attribute Piazzi et al. 2016, DOI `10.1016/j.jmmm.2015.07.055`.
- [x] Pay field-specific-heat/entropy + phenomenological magnetoelastic prior without microscopic-Hamiltonian promotion.
- [x] Attribute Fukamichi/Fujita/Fujieda 2006, DOI `10.1016/j.jallcom.2005.04.022`.
- [x] Pay hydrogen-tuning / MCE / thermal-transport family prior without same-device heat-transfer promotion.

### Task 11: Peer-reviewed POLARIS system acquisition

- [x] Attribute Liang et al. 2026, DOI `10.1016/j.applthermaleng.2025.129144`.
- [x] Encode 131 W/kg specific cooling capacity, plug-in COP 1.0 and 5.4% second-law efficiency at 15 K, plus reported 28.5 K maximum span.
- [x] Encode energetic/hydraulic/acoustic/material measurement campaign and utilization-factor optimization.
- [x] Encode 43-unit commercial deployment / months-long supermarket operation as platform evidence.
- [x] Keep optimized Gd/GdEr working material explicit and block promotion to same-LaFeSi COP/capacity/hydraulic/lifetime closure.

### Task 12: Terminal max-cut and verification

- [x] Record exact remaining same-LaFeSi / STELLAR empirical frontier in `2026-10-15-magnetocaloric-terminal-maxcut.md`.
- [x] Branch is ahead-only of `master` at fresh comparison.
- [x] No pull-request-triggered GitHub Actions workflow exists for the checked head.
- [x] CodeRabbit reached success on the pre-ledger implementation head; re-check final ledger head before any merge claim.
- [x] No Agda compiler is available in this execution environment; no Agda typecheck-success claim is made.
- [x] Validation modules were committed before corresponding evidence owners for newly introduced evidence lanes; executable RED/GREEN remains compiler-bound.

## Terminal hard frontier

1. exact LaFeSi batch chemistry, phase fractions, crystal identity and magnetic symmetry/order;
2. exact-batch M(T,H), S(T,H), c_H(T,H), delta-S and delta-T_ad surfaces;
3. exact LaFeSi B/H field map;
4. exact LaFeSi hydraulic closure;
5. exact LaFeSi heat-transfer/contact/interfacial calibration;
6. exact LaFeSi field/flow/controller timing;
7. completed long-duration same-LaFeSi aging;
8. loaded same-LaFeSi cooling capacity and COP/work decomposition;
9. isolated measured rotational-work-recovery contribution;
10. measured STELLAR field/capacity realization;
11. microscopic Hamiltonian -> bulk free-energy validation if promoted beyond phenomenology.
