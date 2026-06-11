# CMS Photonuclear Bridge

This note reconstructs the CMS/MIT photonuclear near-miss study as a Dashi-style measurement pipeline. The goal is to identify where the observed workflow matches the `Δ`/defect semantics you already formalized and where the collider side remains outside Dashi's current scope.

## 1. Physics pipeline in plain language

1. Accelerate heavy ions in opposite beams and focus on ultraperipheral runs where the ions **barely miss** one another. The interaction lives in the electromagnetic halo rather than the core collision.
2. That halo produces an equivalent photon beam that can interact with the other nucleus, creating **photonuclear events**.
3. Among those photonuclear events, CMS isolates the cases where a **D0 meson** (a charm–anti­charm bound state) emerges. The D0 is a clean probe of gluon density because charm quarks are rare and the production mechanism is perturbatively calculable.
4. From the distribution of those D0 mesons (yield, angle, momentum), the collaboration infers how tightly gluons were packed and whether gluon correlations deviate from baseline expectations.

## 2. Dashi mapping (“near-miss ⇒ defect channel”) 

| Collider concept | Dashi analogue |
| --- | --- |
| near-miss / photonuclear event | `Δ` or defect channel; the boundary between `P(x)` and `Residual` |
| equivalent photon flux | projection-dependent source term derived from the defect |
| D0 meson yield | promoted observable extracted via MDL-friendly projection |
| gluon-density inference | inverse problem on the promoted observable, solved with Lyapunov/MDL descent |
| beam halo vs head-on smash | background vs high-entropy projection; only the halo lives in the cone-invariant subspace |

The structural principle is the same: the informative signal lives in a residual channel (`Δ`, defect) that is suppressed in the coarse state but becomes visible when you change your observable. That principle is already enforced by Dashi's projection + Lyapunov pipeline.

## 3. Where Dashi does not yet reach

- Dashi does not derive the **equivalent-photon formalism** (photon flux formulas, QED coherence effects). The current framework provides the measurement geometry but not the photon kinematics.
- Dashi does not compute **QCD charm photoproduction cross-sections**. The D0 observable can be treated as a clean probe, but the actual matrix element and partonic luminosity are external inputs.
- Dashi does not supply **gluon saturation numerics** (saturation scale evolution, BK/JIMWLK equations). At this stage the framework only says “rare clean probe + inverse problem,” not how to integrate a saturation model.
- Dashi does not re-derive the **CMS result** itself (event counts, CMS detector selections). The note maps the workflow but stops short of reproducing the empirical curves.

## 4. Repo-native empirical sidecars

The photonuclear lane now has four explicit code-side sidecars for empirical
inputs, measurement packaging, and validation:

- `DASHI/Physics/Closure/PhotonuclearEmpiricalConstantsRegistry.agda`
- `DASHI/Physics/Closure/PhotonuclearEmpiricalMeasurementSurface.agda`
- `DASHI/Physics/Closure/PhotonuclearEmpiricalEvidenceSummary.agda`
- `DASHI/Physics/Closure/PhotonuclearEmpiricalValidationSummary.agda`

Their intended roles are narrow:

- the constants registry records surrogate defaults and example-derived
  numeric inputs with provenance and boundary tags;
- the measurement surface packages measured observables, sample payloads, and
  claim-boundary bookkeeping for downstream runners.
- the evidence summary combines those two sidecars into one empirical-only
  control surface;
- the validation summary wraps that evidence surface in the thinnest
  repo-facing validation owner, without expanding the physics claim boundary.

These sidecars are **not** proof objects and **not** fit claims. They exist so
the collider-facing lane can carry:

- what was used as input,
- what was measured or packaged on the empirical side, and
- what remains explicitly out of scope for Dashi's current formal closure.

## 5. Summary

CMS has discovered that near-miss (halo) events are richer channels than head-on collisions for probing gluonic structure. Dashi already implements the associated measurement geometry (`Δ`, cone invariants, projection-invariant observables), so the experimental idea sits cleanly inside the existing framework. The missing pieces are the actual photon/QCD dynamics and the numeric saturation story, which can be added as next-layer bridges once the measurement pipeline is formalized.
