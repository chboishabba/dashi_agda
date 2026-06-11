# Embodied Motor Multisensory Bridge

This bounded Animalexic biology-stack receipt adds
`DASHI.Biology.EmbodiedMotorMultisensoryBridge`.

The Agda surface models these channels as receipt-gated observations:

- motor control and effector state;
- pain/nociception as a behavioral class, not pain qualia;
- proprioceptive signal;
- vestibular signal;
- multisensory body estimate;
- constrained behavior envelope and motor-policy constraint.

## Non-Promotion Guards

The module explicitly carries these guards:

- `NoIntentRecoveryClaim`
- `NoPainQualiaIdentityClaim`
- `NoFullMotorPolicyClaim`
- `NoSensorFusionClosureClaim`

Additional guard constructors block single-channel diagnosis and species-wide
motor lexicon claims.

## Integration Note

The module now carries canonical toy inhabitants for the Animalexic surface,
embodied surface, observation, multisensory integration, promotion gate, and
non-promotion certificate.  These inhabitants are diagnostic type witnesses,
not empirical animal-behaviour receipts.

This file is imported by `DASHI.Biology.BioAnimalexicStackDischarge` and the
aggregate `DASHI.Everything` surface.
