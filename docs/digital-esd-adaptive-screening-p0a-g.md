
# Digital-ESD adaptive screening P0-A through P0-G

Status: source-written implementation/runbook.

This workflow makes the 43,996-record ERIC screening surface computationally
tractable while preserving the authoritative title/abstract screening ledger
and every unresolved/excluded record. Machine/model output never becomes
screening authority.

## Canonical authority chain

~~~
exact deduplicated universe
        ↓
authoritative screening ledger
        ↓
candidate-only adaptive work allocation
        ↓ explicit review overlay
authoritative screening ledger
        ↓
include / probable only
        ↓
full-text retrieval
        ↓
canonical SLR evidence / review
        ↓
independent SourceAuditAdmission
~~~

Formal owner:
DASHI/Education/DigitalESDAdaptiveScreeningProgrammeExact.agda

Regression:
DASHI/Education/DigitalESDAdaptiveScreeningProgrammeRegression.agda

Existing owners reused rather than replaced:
- DigitalESDTitleAbstractScreeningExact
- DigitalESDEligibilityFrameExclusionExact
- AdmissibleConsumerMDLHyperfabricExact
- NDimParetoHyperfabricExact
- DigitalESDSearchToSourceAuditAdmissionExact
- DigitalESDSLRSourceReviewBridgeExact

Constructive collisions prove:

~~~
same machine candidate surface
!= determinate reviewed screening decision

same publication-similarity surface
!= determinate same-empirical-study identity
~~~

## P0-A — exact universe and denominator integrity

Run:

~~~bash
python3 scripts/prepare_digital_esd_screening_ledger.py   --input artifacts/digital-esd/deduplication/eric-deduplicated-records.json   --out-dir artifacts/digital-esd/screening
~~~

Expected current ERIC denominator: 43,996 exact deduplicated records.

The formal runtime receipt requires emittedReceiptCount ≡ inputRecordCount.
Every input stays either pendingReview or reviewedDecision decision. Unreviewed
records cannot disappear from the denominator.

## P0-B / P0-C — candidate assessment and study-family hypotheses

Run:

~~~bash
python3 scripts/assess_digital_esd_screening_candidates.py   --metadata artifacts/digital-esd/deduplication/eric-deduplicated-records.json   --ledger artifacts/digital-esd/screening/screening-decisions.jsonl   --out-dir artifacts/digital-esd/screening/adaptive
~~~

Outputs:
- candidate-assessments.jsonl
- study-family-hypotheses.jsonl
- study-family-fibres.jsonl
- assessment-manifest.json

Candidate assessment uses cheap deterministic title/abstract signals only to
construct a review aid.

~~~
candidate decision != authoritative screening decision
candidate exclusion != exclusion
candidate confidence != source quality
~~~

Study-family candidate fibres use:
- exact DOI
- exact normalised title
- blocked fuzzy title within first-author/year cells

Exact DOI/title blocks use representative-star edges rather than all-pairs
edges so large duplicate blocks do not produce quadratic output.

~~~
metadata duplicate
!= publication duplicate
!= report-family duplicate
!= same empirical study
~~~

No similarity rule constructs sameEmpiricalStudy.

## P0-D / P0-E / P0-F — calibration, diagnostics and Pareto queue

Run:

~~~bash
python3 scripts/select_digital_esd_screening_pareto.py   --ledger artifacts/digital-esd/screening/screening-decisions.jsonl   --assessments artifacts/digital-esd/screening/adaptive/candidate-assessments.jsonl   --fibres artifacts/digital-esd/screening/adaptive/study-family-fibres.jsonl   --out-dir artifacts/digital-esd/screening/adaptive
~~~

Calibration strata:
- obviousIncludeCandidate
- obviousExcludeCandidate
- highUncertaintyCandidate
- highDuplicateAmbiguity
- rareTerminologyOrSourceType
- missingAbstractOrMalformedMetadata

Outputs:
- calibration-selection.jsonl
- calibration-estimate.json
- screening-pareto-queue.jsonl
- pareto-manifest.json
- screening-process-audit.json

Calibration diagnostics are computed only over records already carrying
authoritative review decisions. The candidate false-negative quantity is a
reviewed-subset proxy, not a population error rate or threshold.

~~~
calibration estimate != source truth
calibration estimate != population truth
calibration estimate != screening decision
~~~

The queue reuses DASHI's existing N-dimensional Pareto semantics.

Five declared axes:
- information-gain loss
- likely corpus-contraction loss
- rare-cell coverage loss
- duplicate-family payoff loss
- reviewer cost

There is no scalar weighted score. Dominance is computed over the small set of
unique cost vectors, not pairwise over 43,996 records.

The process audit exposes reviewed/unresolved counts, missing abstracts,
pending records by publication type and Pareto-front composition by stratum.
Those are process-visibility coordinates only; they do not establish bias,
harm, source quality or eligibility-frame truth.

## Explicit review loop

Reviewer/model suggestions are not authoritative. Explicit reviewer decisions
are written to reviewer-decisions.jsonl and then applied through the existing
ledger compiler.

~~~bash
python3 scripts/prepare_digital_esd_screening_ledger.py   --input artifacts/digital-esd/deduplication/eric-deduplicated-records.json   --decisions artifacts/digital-esd/screening/reviewer-decisions.jsonl   --out-dir artifacts/digital-esd/screening
~~~

Then rerun P0-B through P0-F.

~~~
authoritative ledger
→ candidate analysis
→ calibration / Pareto queue
→ explicit review
→ append/supersede authoritative decisions
→ regenerate ledger
→ recompute candidate analysis
→ ...
~~~

The candidate layer never directly writes an exclusion or inclusion.

## Review-process absence probes

The formal owner asks:
1. who/practices/source genres could be absent because frozen query vocabulary
   did not name them;
2. which retrieved records lack usable title/abstract metadata;
3. whether ranking systematically delays particular populations, terms, source
   roles or publication forms;
4. which source types occupy sparse cells;
5. which community/disciplinary terminology lies outside the seven frozen
   query families.

These are frame/missingness probes, not automatic bias or harm claims.

## P0-G — retained/probable full-text escalation

Only authoritative include and probable decisions have constructors for
RetainedForFullText.

Prepare the worklist:

~~~bash
python3 scripts/prepare_digital_esd_fulltext_handoff.py   --ledger artifacts/digital-esd/screening/screening-decisions.jsonl   --out-dir artifacts/digital-esd/fulltext
~~~

After retrieval, supply retrieved-artifacts.jsonl with source identity, artifact
path, SHA-256, retrieval receipt/time, manifestation family and optional
materialised text path. Then run:

~~~bash
python3 scripts/prepare_digital_esd_fulltext_handoff.py   --ledger artifacts/digital-esd/screening/screening-decisions.jsonl   --retrieved artifacts/digital-esd/fulltext/retrieved-artifacts.jsonl   --verify-files   --out-dir artifacts/digital-esd/fulltext
~~~

Outputs:
- canonical-fulltext-evidence.jsonl
- slr-source-unit-adapter.jsonl
- fulltext-handoff-manifest.json

Canonical evidence preparation retains the screening decision reference,
artifact SHA-256, manifestation reference, source revision, content digest,
retrieval receipt and WholeRevision anchor. It remains candidate-only and
non-promoting.

The Python SLR adapter row is emitted only when an explicit materialised
text_path exists. It remains a compatibility execution adapter, not the
production semantic ABI.

P0-G still requires the existing downstream payments:

~~~
canonical full-text evidence
→ SLR review packet
→ situated audit observations
→ independent SourceAuditAdmission
→ CorpusAuditedSource
→ hyperfabric / framework challenge
~~~

Full-text retrieval creates none of those authorities.

## Current certification boundary

The P0-A–G formal owner and runtime tools are source-written on the adaptive
screening branch. The 43,996-record artifacts are intentionally not committed
to the remote branch, so this environment has not executed the real corpus
loop.

Do not mark a runtime stage paid until its exact artifacts/counts/hashes are
observed locally.


## P0-G final audit / framework challenge carrier

The formal owner continues beyond full-text handoff using existing domain owners.

For each admitted source:

~~~
SLRAssistedCorpusAuditedSource source
+
SourceAuditHyperfabric source
+
one existing TransformativePrincipleMatrix row
        ↓
FrameworkChallengeReceipt source
~~~

Allowed dispositions:

- supportsCandidatePrinciple
- narrowsCandidatePrinciple
- splitsCandidatePrinciple
- mergesCandidatePrinciple
- defeatsCandidatePrinciple
- extendsCandidatePrinciple
- unresolvedFrameworkChallenge

The challenge keeps source-specific evidence references and reasoning. It cannot
create final principle promotion and one source cannot manufacture a corpus
conclusion.

Corpus-level revision is represented separately by
CorpusFrameworkRevisionReceipt and requires its derivation stage to be exactly:

structuredCorpusChallengeAndRevision

from DigitalESDTransferablePrincipleDerivationMethodExact.

This preserves:

~~~
source challenge != final corpus synthesis
framework revision != universal truth
candidate framework before review != final review result
~~~


## Actual scholarly-paper parsing / processing ledger

P0-G is now connected to the generic SLR scholarly parser through
`interop_scripts/digital_esd/run_verified_fulltext_parse.py`.

The wrapper emits an exact per-study processing ledger:

```text
study-processing-ledger.jsonl
study-processing-ledger-manifest.json
```

with one row for every metadata record and explicit stage containment. It also
emits:

```text
fulltext-retrieval-residual.jsonl
fulltext-retrieval-residual-manifest.json
```

containing only authoritatively retained include/probable records that still
lack verified full-text artifacts.

The current observed smoke specimen is ERIC `EJ1083370`: one verified
full-text artifact was materialised, handed to the SLR scholarly parser and
successfully parsed; neither reviewed canonical evidence nor
`SourceAuditAdmission` was created. The remaining metadata denominator is not
relabelled as parse failure.

This makes the next operational frontier explicit: retrieve more retained
full-text artifacts, then rerun the same wrapper. No new Digital-ESD parser
architecture is required for ordinary PDF/DOCX/HTML/TXT studies.
