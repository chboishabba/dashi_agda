# Magnetocaloric Terminal Max-Cut Record

**Parent plans:**
- `docs/superpowers/plans/2026-10-14-magnetocaloric-amr.md`
- `docs/superpowers/plans/2026-10-15-magnetocaloric-consumer-integration.md`

## Completed acquisition / formalisation cuts

- [x] Canonical attribution migrated to `DASHI.Core.AttributedSourceCore`; access carriers, authorship, claim role, authority and DASHI reconstruction remain separate.
- [x] Same-study 2025 LaFeSi material identity captured: VACUUMSCHMELZE Mn-substituted, fully hydrogenated microchannel regenerators with a bounded approximate composition envelope.
- [x] Same-study evidence payments captured separately for six-week aging, preliminary three-month microchannel preservation, 1 T adiabatic-temperature characterization and the load-free ~288 K / 2 Hz / ~0.8 T aging operating point.
- [x] Months-to-years LaFeSi aging remains explicitly future work, not promoted to lifetime evidence.
- [x] Cross-object La-Fe-(Mn)-Si-H family atlas added from Radulov 2017, Krautz 2014, Piazzi 2016 and Fukamichi/Fujita/Fujieda 2006.
- [x] Family evidence pays NaZn13 crystal/transition prior, Mn/Si/H tuning, specific-heat/entropy magnetoelastic prior and thermal-transport prior without promoting to exact MAGNOTHERM batch identity.
- [x] Peer-reviewed 2026 POLARIS device evidence added from Liang et al., DOI 10.1016/j.applthermaleng.2025.129144.
- [x] POLARIS payments capture measured system performance, hydraulic/system characterization and commercial deployment.
- [x] POLARIS optimized Gd/GdEr performance is explicitly blocked from promotion to same-material LaFeSi COP/capacity/lifetime.
- [x] Vendor claims remain separately typed: up-to-30% rotational work-recovery claim; STELLAR 5 T target; 125 kW+ module vision; 250 kW+ two-module depiction.
- [x] NS and YM remain structural precedents only.
- [x] All evidence layers are wired into `DASHI.Physics.Thermodynamics.Everything` and the terminal consumer/max-cut receipts.

## Current terminal hard frontier

The remaining max-cut is physical same-object identification/calibration, not missing generic formal structure:

1. exact LaFeSi batch chemistry, phase fractions, crystal identification and magnetic symmetry/order;
2. exact-batch M(T,H), S(T,H), c_H(T,H), delta-S and delta-T_ad surfaces with uncertainty and B/H convention;
3. exact LaFeSi spatial/temporal field map and constitutive B-H convention;
4. exact LaFeSi pressure-drop/flow porous closure;
5. exact LaFeSi solid-fluid heat-transfer/contact/interfacial calibration;
6. complete same-LaFeSi field/flow/controller phase timing and error envelope;
7. completed long-duration same-LaFeSi aging approaching product-life timescales;
8. loaded same-LaFeSi cooling capacity and first-law COP accounting including motor/pump/field/parasitic/recovered work;
9. isolated measured contribution of rotational work recovery to the vendor's up-to-30% claim;
10. measured STELLAR field/capacity realization rather than development targets;
11. microscopic/electronic Hamiltonian -> ensemble -> bulk free-energy validation if the quantum-first route is to be promoted beyond a phenomenological model.

## Verification state

- [x] Fresh branch comparison after the acquisition pass: feature branch is 68 commits ahead and 0 behind `master`, with 32 changed files (+2844/-0).
- [x] CodeRabbit reports success on head `07651f339f46d7da00abaf02de4115cdc8fc3f12`.
- [x] No pull-request-triggered GitHub Actions workflow exists for the checked implementation head.
- [x] No Agda compiler is available in this execution environment; no Agda typecheck-success claim is made.
- [x] GitHub mergeability was still reporting false on head `07651f339f46d7da00abaf02de4115cdc8fc3f12` at the final status read; no merge-ready claim is made from branch-ahead or CodeRabbit status alone.
- [x] Validation modules were committed before their corresponding implementation owners where new evidence lanes were introduced; executable RED/GREEN verification remains compiler-bound.

This record is a non-promoting implementation ledger. It does not convert cited literature, vendor statements, static review, or source acquisition into theorem authority or same-device calibration.
