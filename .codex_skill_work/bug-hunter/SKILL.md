---
name: bug-hunter
description: Systematically reproduces, diagnoses, and fixes bugs using a structured reproduce → isolate → patch → validate loop. Companion skill in the get-shit-done stack.
metadata:
  short-description: Reproduce, diagnose, patch, and verify bugs
---

```md
# Bug Hunter Skill

This skill performs structured debugging. It exists to prevent guess-fix behavior.
It should usually be entered from `get-shit-done`, `long-running-development`, or `orchestrator` once a concrete failure exists.

## Canonical inputs and outputs

Read first:

- `spec.md`
- `architecture.md` if relevant
- `plan.md`
- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`

Update as needed:

- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`
- regression tests when appropriate

## Debugging loop

1. Reproduce the bug before editing code.
2. Capture the failing command, test, logs, and stack traces.
3. Isolate the smallest failing unit and identify root cause.
4. Implement the minimal fix.
5. Re-run validation and regression checks.
6. Record the failure, fix, and evidence.

If the bug cannot be reproduced, stop and collect more context instead of guessing.

## Companion skill integration

- `get-shit-done`: canonical entrypoint for project framing and state normalization.
- `architect-planner`: use if the failure reveals an architectural flaw rather than a local defect.
- `repo-auditor`: use if the bug suggests broader spec drift or coverage gaps.
- `long-running-development`: return there when the fix is part of an active milestone.
- `context-manager`: use before handoff if the debugging trail is long or noisy.
- `orchestrator`: use when repeated reproduce/fix/validate cycles must be supervised across phases.

## Completion criteria

- The failure was reproduced.
- Root cause was identified.
- The fix resolved the failure.
- Validation passed.
- Any new regression coverage was added or consciously skipped with justification.
```
