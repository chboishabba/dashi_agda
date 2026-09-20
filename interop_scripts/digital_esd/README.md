# Digital-ESD interop scripts

This directory contains application-side delegates only.

The generic ERIC parser, screening work-queue runtime, reviewed-decision
application, full-text verifier, SLR handoff, and study-processing census live
in the `slr` repository.

`run_l1_l3.py` delegates to the generic SLR driver and deliberately does not
copy or reimplement those semantics.

Example:

```bash
python3 interop_scripts/digital_esd/run_l1_l3.py \
  --slr-root ../slr \
  --export-root /path/to/retained-eric-exports \
  --artifact-root artifacts/digital-esd/real-eric
```

Without a reviewed decision overlay the run parses/deduplicates ERIC metadata,
builds candidate assessments/Pareto work queues, and emits human review packets,
but does not claim any source has been genuinely screened.

To advance authority:

```bash
python3 interop_scripts/digital_esd/run_l1_l3.py \
  --slr-root ../slr \
  --export-root /path/to/retained-eric-exports \
  --artifact-root artifacts/digital-esd/real-eric \
  --decision-overlay /path/to/completed-reviewed-decisions.jsonl
```

A retrieved-manifest may then be added to verify include/probable full text.
Later SLR parse/review/SourceAuditAdmission receipts may also be supplied to
the generic census; absent receipts remain zero.


## Scholarly full-text parsing vertical slice

The current ERIC parser is a **metadata/title/abstract parser**, not a parser of
the retained studies themselves.

The ESD-4 scholarly full-text path is now formalised by:

`DASHI/Interop/DigitalESD/ScholarlyFullTextCrossPollinationExact.agda`

with execution/reconciliation owner:

`DASHI/Interop/DigitalESD/ScholarlyFullTextInteropExecutionExact.agda`.

The application-side reference implementation is deliberately split:

```text
scholarly_fulltext.py
    exact artifact/revision/digest preparation
    configured parser invocation
    returned-node/facet verification

scholarly_parser_prototype.py
    prototype document extraction
    prototype generic scholarly facet candidates
```

The prototype is **not** the production semantic ABI.  It exists to generate
real fixtures and expose which generic parser capabilities should later move
into SLR.

### Run one retained full-text tranche

Prepare exact requests from the full-text cache/canonical handoff:

```bash
python3 interop_scripts/digital_esd/scholarly_fulltext.py prepare \
  --input artifacts/digital-esd/fulltext/cache-ledger.jsonl \
  --output artifacts/digital-esd/scholarly/requests.jsonl \
  --verify-files
```

Run the current application-side prototype through the generic invocation
boundary:

```bash
python3 interop_scripts/digital_esd/scholarly_fulltext.py run \
  --input artifacts/digital-esd/scholarly/requests.jsonl \
  --config interop_scripts/digital_esd/scholarly_fulltext.prototype.json \
  --output-dir artifacts/digital-esd/scholarly/run
```

Verify its output against the Agda contract:

```bash
python3 interop_scripts/digital_esd/scholarly_fulltext.py verify \
  --requests artifacts/digital-esd/scholarly/requests.jsonl \
  --parser-output artifacts/digital-esd/scholarly/run/parser-output.jsonl \
  --output artifacts/digital-esd/scholarly/verified.jsonl
```

For a deliberately bounded tranche, add `--allow-partial` to verification.
Partial parsing is then explicit rather than silently presented as corpus
completion.

The prototype currently supports TXT/Markdown, HTML, DOCX, and PDF. PDF
extraction requires either `pypdf` or PyMuPDF/`fitz`.

### What is emitted

Document parsing produces revision-anchored nodes:

```text
section / heading / paragraph / sentence
table / table-cell
figure / caption
reference entry / appendix
```

using canonical text-range or structured-coordinate spans.

Candidate scholarly facets include:

```text
Study
Population
Sample
Intervention
Comparator
Outcome
StudyDesign
Setting
TimePeriod
Method
Limitation
Funding
Institution
ParticipantGroup
Measurement
```

Every facet is represented as a candidate canonical observation with exact
revision/span identity.

The authority boundary remains:

```text
parser output != reviewed observation
candidate facet != study truth
successful process != evidence payment
verified parser bundle != SourceAuditAdmission
```

The next scientific step is to run this over a **small heterogeneous set of
real retained ERIC studies** and inspect extraction failures before promoting
any reusable parser logic into SLR.
