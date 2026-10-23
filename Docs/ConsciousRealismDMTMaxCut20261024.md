# Conscious realism × DMT — max-cut formalisation (2026-10-24)

Status: **Agda source-written / kernel-unverified**; **exact synthetic arithmetic executed**; no clinical, neural, DMT, or external-entity evidence is claimed.

## Attribution ledger (original authors own their results)

- **Hoffman and Prakash (2014)** — *Objects of Consciousness*, DOI 10.3389/fpsyg.2014.00577. Conscious-agent probabilistic perception/decision/action.
- **Hoffman, Prakash and Prentner (2023)** — *Fusions of Consciousness*, DOI 10.3390/e25010129. Qualia kernel Q=DAP, fusion.
- **Hoffman, Prakash and Chattopadhyay** — *Traces of Consciousness*, https://www.preprints.org/manuscript/202410.1305 (preprint posted in 2024; the Trace Institute calls this a 2025 trace-chain result). Trace-chain theorem and trace order.
- **Gallimore, Hermansson and Hoffman (2026)** — *Traces of the Other*, DOI 10.31234/osf.io/8qvgy_v2. DMT-interface and independent-agent **hypotheses**, proposed experiments, no confirmation.
- **Jan-Cordón (2026)** — *The Trace Term as the Empirical Target*, DOI 10.2139/ssrn.7139998. Independent commentary on unidentified cooperation/semantic/temporal nuisances, not experimental results.
- **DASHI (this cut)** — abstract factorisation proof, observation-equivalence no-decoder, noncooperation countermodel, exact finite synthetic arithmetic and proposed experiment.

Attribution firewall: source citation is provenance, not imported proof; source publication is not independent replication; formalisation is not scientific authorship; a stochastic kernel is not a measured brain/qualia identification; a mathematical interpretation is not a clinical discovery. The source atlas uses the existing AttributedSourceCore.

## Theorem cut and scope

**1. Unrestricted observable-law non-identifiability.** Every finite row-stochastic Q can be written Q=DAP using action/world spaces equal to the experience space and D=Q, A=P=I. Two differently tagged internal/external hypotheses can therefore share identical Q. No function of Q alone can correctly recover both different tags. The Agda owner ConsciousRealismDMTIdentifiabilityExact proves generic identity factorisation in a supplied kernel-composition algebra and the decoder impossibility. Normalization and semantic/physical meaning must be separately justified. This does NOT disprove or establish external conscious agents.

**2. Fixed-kernel trace-of-trace consistency.** For row-stochastic Q and observed V, hidden H, under almost-sure return and invertibility:

    T_V(Q) = Q_VV + Q_VH (I - Q_HH)^(-1) Q_HV

For nested V0 within V1 of the SAME kernel, T_V0(T_V1(Q)) = T_V0(Q). This follows from first-return sampling (original trace-chain literature); it does not distinguish conscious realism from classical hidden Markov models. It does NOT require T_V0(Q_sober)=T_V0(Q_DMT) when DMT changes the kernel. The exact Python fixture witnesses this: direct and nested are both [[33/56,23/56],[7/20,13/20]]; an altered Q yields [[137/280,143/280],[7/20,13/20]]. Tested with 128 additional positive rational cases. The cases are synthetic, and not a general kernel-certified Agda trace theorem.

**3. Cooperation-zero no-go.** An external-story mixture with probability of cooperation r has P1=(1-r)P0+r Psignal. When r=0, P1=P0 exactly: a null cannot universally exclude all such unrestricted alternatives. A newly RESTRICTED model with independently calibrated lower bounds r>=r_min>0 and p_signal>=p_min>1/2 predicts p_correct >= 1/2 + r_min (p_min-1/2). Synthetic example r_min=1/4, p_signal=3/4 gives p_correct>=9/16; none of these numbers was estimated from DMT data. A trial has discriminating force only for the preregistered restricted alternative and with adequate power.

**4. Prior-art reuse.** Reuse DASHI.Core.FiniteStochasticBisimulationExact (a defect from current observation to future law), DASHI.Cognition.PNF.RationalMarkovLumpingFutureExact, DASHI.Core.DashiMarkov, DASHI.Reasoning.MultiObserverScienceQuotient and the existing Kluver/5HT2A sources. None presently establishes a measured DMT concentration-to-qualia-kernel map; do not rebuild them as competing numbered shells.

## Exact audit and reproducibility

Run: python3 scripts/audit_conscious_realism_dmt_trace.py

Standard-library exact Fraction arithmetic verifies: row stochasticity; inverse-based first-return traces; nested-set consistency in 129 synthetic fixtures; nonzero hidden excursion contribution; changed-Q counterexample; QII identity; zero-cooperation equality; restricted example 9/16; and one-sided Binomial(n=64,k=48,p=1/2) tail 713250450657109/18446744073709551616. This tail is a **worked synthetic number**, not an observed result or a trial-size recommendation. The script computes its own JSON receipt and needs no random library, network, or data downloads.

Potential Agda commands, **not claimed run**:
- agda -i . DASHI/Cognition/ConsciousRealismDMTSourceAtlasExact.agda
- agda -i . DASHI/Cognition/ConsciousRealismDMTIdentifiabilityExact.agda

## A discriminating preregistered experiment

- Primary estimand: agreement of a prospectively committed, uniformly randomized concealed binary target Z with timestamped, locked, independently and blindly scored response R. Freeze the target, scoring dictionary, exclusions, trial denominator, sample size, stop rule and analysis before unblinding.
- Under fixed n, independent chance Bernoulli(.5) trials, use the exact binomial one-sided tail. For clustered, missing, adaptive or selectively reported trials, this tail is INVALID; prespecify a matched hierarchical/randomization analysis.
- Ensure blinding of participant, session staff and analysts; sealed generation, machine-verifiable target commitments, independent score validation, synchronized clocks, leakage/security audit, no post hoc narrative scoring, placebo/sham and negative controls, and complete reporting of failures.
- Secondary: independently controlled cross-participant target transfer; valid pre-treatment-covariate conditional dependence; calibrated neural state-to-report mappings; held-out fixed-Q trace checks; controlled interventions; externally replicated predictive comparison with matched model complexity. No inference from mere shared cultural motifs or recurring entity descriptions.
- Only compare constrained internal and external model classes with independently justified exclusions. Overly expressive stochastic generators can fit the same distribution. Even repeated above-chance findings establish at most a need to investigate an unexplained information channel, not entity consciousness.
- Human DMT work requires institutional ethics approval, qualified clinicians and legal/safety oversight. This repository does not provide drug administration instructions.

## Pareto frontier / live debt

| Rank | Deliverable | Actual status | Missing admission evidence |
|---|---|---|---|
| P0 | Named attribution/source-role ledger | Implemented source-written atlas | Version-specific updates as needed; copies are one lineage |
| P0 | Generic kernel nonidentifiability + noncooperation | Agda source-written, unverified | Kernel typecheck, physical semantics remain open |
| P0 | Finite trace and counterexample | Exact Python synthetic computation passed | Actual aligned observations and return statistics |
| P1 | Same-object DMT concentration → receptor/neural measurement → (P_c,D_c,A_c) → Q_c | Open | Calibrated measured parameters, validated observation map, prospective out-of-sample fit |
| P1 | Preregistered hidden-target experiment | Design ready; **not executed** | Independent ethical/legal approval, blinded data, adequate registered power, replication |
| P1 | Distinguish *restricted* internal/external models | Conditional inequality, not model-specific proof | Independently justified restrictions plus measurement and held-out exclusion |
| P2 | Full local finite trace theorem | Attributed external source theorem, synthetic witnesses only | Prove all stochastic normalization/return conditions in kernel |
| P2 | Existence of independent DMT entities | **Not established** | Even a signal requires ordinary-channel exclusion and replication; ontology remains nonunique |

**Max-cut conclusion:** The mathematical obstruction is observational equivalence, so further nominal restatements have low alpha. The decisive unresolved bridge is independently constrained, calibrated, same-object physical and information-theoretic measurement. Cite original authors for source mathematics and hypotheses, DASHI for derivations, and no one for empirical claims that have not been observed.
