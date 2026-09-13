# Twenty-Scientist Scientific Operator Factorisation Design

## Goal

Factor the existing twenty scientist-specific science fibres through a small set of reusable scientific operator families, while preserving domain-specific semantics, source provenance, reverse obligations, and the two existing gated fibres.

## Scope

This tranche is science-only. It does not add event, custody, motive, succession, or historical-programme claims.

The current branch already has twenty scientist-specific science kernels and 18 finite-or-stronger implementations. The next step is to identify reusable scientific operators that several fibres can legitimately share without equating their empirical mechanisms.

## Operator families

1. **Weak-signal inverse inference**
   - Grillmair, Hicks, Zhang Xiaoxin, Maiwald, Jason Thomas.
   - Shape: observation field -> filter/decomposition -> candidate latent structure -> constrained inverse fibre -> next-measurement obligation.

2. **Resilient sensing/control/verification**
   - LeBlanc, McCasland, Zhang Daibing, Chen Shuming, Yan Hong.
   - Shape: environment/state -> sensing/verification/estimation -> control/action -> response/failure residual.

3. **Materials/process/structure-property**
   - Monica Reza, Zhou Guangyuan, Fang Daining.
   - Shape: design/process coordinates -> latent material/structural state -> property vector -> reverse admissible-design fibre.

4. **Molecular spectroscopy/chemical biology**
   - Maiwald, Jason Thomas, Li Minyong.
   - Shape: excitation/perturbation -> molecular/target state -> measured readout -> target/configuration inference.

5. **Field/plasma/precision-force discrimination**
   - Nuno Loureiro, Ning Li, Amy Eskridge.
   - Shape: field/material state -> governing model/apparatus -> observable -> comparator/null-test residual.
   - Amy remains programme/authorship-gated and must not be promoted to executable science.

6. **Classification/evidence/governance**
   - Feng Yanghe, Liu Donghao, with Chen Shuming as an overlapping verification fibre.
   - Shape: uncertain input/evidence -> classification/assessment -> evidence-bearing decision state.

Anthony Chavez remains identity-gated. His accelerator-engineering science must not be inherited across the missing-person/LANL identity seam until that prerequisite is paid.

## Core abstraction

Create `DASHI/Core/ScientificOperatorFamilyExact.agda` with:

- `ScientificOperatorFamily` enumerating the six families above;
- `ScientificOperatorShape` carrying input-role, transform-role, output-role, and reverse-obligation descriptions;
- a bounded `OperatorFactorisation` record from a named scientist science fibre into one operator family;
- explicit firewalls that family factorisation does not imply identical equations, same empirical mechanism, same historical programme, collaboration, or common cause.

Reuse existing `DASHI.Core.QueryFactorisationSufficiency` terminology rather than inventing a new generic factorisation theorem. The new owner is a science taxonomy/factorisation registry, not a replacement for query-factorisation semantics.

## Family adapters

Create one focused owner per family under `DASHI/Culture/` that binds current scientist science kernels to the operator shape and records the family-specific reverse scientific leaf. Each adapter must retain the original domain owner and may overlap: e.g. Maiwald legitimately factors through both weak-signal inverse inference and molecular spectroscopy.

## Coverage ledger

Create `MissingDeceasedTwentyScientistScientificOperatorFactorisationExact.agda` with exactly 20 scientist rows. Each row contains:

- person;
- list of operator families;
- current domain owner;
- factorisation status (`paid`, `gated`);
- next scientific implementation leaf.

The ledger must prove/record:

- count = 20;
- every scientist is represented;
- 18 are science-factorised;
- 2 are explicitly gated (Chavez identity, Amy authorship/programme);
- overlapping families are allowed;
- operator-family sharing does not imply same mechanism or collaboration.

## BIDI integration

Create `MissingDeceasedTwentyScientistScientificOperatorBidiExact.agda` that projects:

forward:

`scientist science fibre -> operator family -> reusable scientific role`

and reverse:

`desired scientific role -> candidate scientist/operator fibres -> missing scientific coordinates`.

This BIDI layer is for scientific reuse only. It cannot manufacture provenance, historical deployment, person possession, custody, or event causation.

## Verification

TDD contract first. Static checker must require:

- core operator owner;
- six family adapters;
- all-20 factorisation ledger;
- BIDI owner;
- fixed counts 20/18/2;
- explicit cross-family and historical firewalls;
- aggregate imports.

No Agda/kernel success claim without an actual compiler/workflow receipt.
