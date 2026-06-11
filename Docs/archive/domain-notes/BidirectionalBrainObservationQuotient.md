# Bidirectional Brain Observation Quotient

This note records the local theorem-thin surface added in
`DASHI/Physics/Closure/BidirectionalBrainObservationQuotient.agda`.

The purpose is to keep the brain lane honest while making the archive-backed
brain/body observation join explicit.

## Core Object

The module models a latent brain/body carrier:

```text
sigma_t
```

with multiple lossy observation maps:

```text
pi_fMRI(sigma)
pi_percept(sigma)
pi_behavior(sigma)
pi_bodyResource(body)
```

These are typed as many-to-one quotient channels. The module does not treat any
one channel as an injective readout of latent state.

## Joint Inference

The intended admissible claim is:

```text
joint observations may narrow [sigma]
```

where `[sigma]` is an observational equivalence class.

The explicit non-claim is:

```text
joint observations recover sigma
```

The Agda surface represents this with `JointInferenceNarrowing`: each separate
channel has a residual class, and the joint class is allowed to be narrower
than fMRI, percept, behavior, or body-resource classes alone. The joint class is
still a quotient and `noUniqueStateRecoveryFromJointClass` is pinned to
`true`.

## Whole-Body Resource Gate

The module includes a whole-body resource constraint surface over:

```text
blood flow
oxygen
glucose
thermal load
cardiovascular work
```

The point is not to solve physiology. The point is to block brain-only
quantitative physiology claims by requiring body-resource residuals to feed
neural admissibility.

## Non-Promotion Boundary

The canonical boundary marks all of the following as false:

```text
fMRIIsPercept
reportIsGroundTruth
qualiaClosure
cognitionClosure
latentStateRecovery
empiricalValidationClosed
```

Allowed wording:

```text
fMRI, perceptual report, behavior, and whole-body resource readouts can be
modeled as complementary lossy quotients of latent brain/body dynamics.
```

Forbidden wording:

```text
fMRI is the percept.
Report is ground truth.
Joint inference recovers the latent neural state.
The module proves qualia, cognition, consciousness, or empirical brain closure.
```

## Relation To Existing Brain Lane

`BrainConnectomeFMRIObservationQuotient.agda` remains the local fMRI-facing
observation target:

```text
phase orbit class
-> neural state initialization
-> connectome-constrained processing
-> laminar / high-resolution fMRI readout
-> behavioral report
```

`BidirectionalBrainObservationQuotient.agda` adds the complementary quotient and
body-resource layer around that target:

```text
latent brain/body state
-> lossy fMRI / percept / behavior / resource quotients
-> narrowed observational equivalence class
-> non-promoting boundary
```
