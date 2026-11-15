# NV photon two-shot readout max-cut — 26 October 2026

## Scope
The repository already contains the true NV Bernoulli likelihood owner in diamond MCG #1238, same-object zero-field collision in stacked #1269, and generic statistical decision/evidence distinction in `DASHI/Statistics/BinaryTestDecisionDirectionalEvidenceExact.agda`.

New `NVPhotonTwoShotKernelExact.agda` intentionally introduces only the **conditional i.i.d. product-law consumer** of the existing one-shot likelihood. This is not a measured independence claim, an invented Poisson process, a time-series likelihood or a generic new probability ontology.

## Exact formal content
With `p = P(click)`, `q = P(dark)` and source witness `p+q=1`, define the two-click outcomes on the source photon response:
- `P(click,click)=p²`;
- `P(click,dark)=pq`;
- `P(dark,click)=qp`;
- `P(dark,dark)=q²`.

The finite polynomial square and original one-shot normalized likelihood prove the joint sum equals one. A two-shot threshold decoder emits `bothClick`, `bothDark`, or `tie`; its outcome probabilities `p², q², pq+qp` also sum to one. One-click histories remain **ambiguous**, and cannot be advertised as perfect classification.

To compare two prepared states (+1 and -1), instantiate the kernel separately with each state's original `ConditionalPhotonModel.response`. If the photon distributions are identical, no number of i.i.d. repeats separates the states. If distinct, quantitative multi-trial bounds require a proved composition theorem (binomial law / likelihood ratio or suitable concentration bound) plus the physical independence assumptions. This tranche does not promote such a bound.

## Critical experiment gate
Repeated measurements need independent state preparations or a source-validated conditional dependence model; readout of the same continuously evolving spin is not automatically i.i.d. Calibration must include repumping/optical back-action, detector dead time, drift, correlation times, batch effects, click/no-click threshold, photon background, observation duration, and held-out tests. MCG cardiac sensitivity is not photon-state readout fidelity.

## Provenance
Mathematical product probability and Bernoulli identities: standard finite probability; exact finite Agda compilation by DASHI formalisation in #1269. Existing NV sensor and data attribution: parent #1238; no original physics priority claimed by this bridge.

Proof status: source-written, Agda kernel check not performed; CI intentionally out of scope.
