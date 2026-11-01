---
name: repo-auditor
description: Performs a systematic audit of a repository against a specification, architecture guide, or requirement list. Companion skill in the get-shit-done stack.
metadata:
  short-description: Audit spec versus implementation across the repo
---

```md
# Repository Audit Skill

This skill performs a full repository audit against a specification or architecture guide.
It should usually be invoked from `get-shit-done` or `orchestrator`, using the canonical project memory they maintain.

## Canonical inputs and outputs

Read first:

- `spec.md`
- `architecture.md`
- `plan.md`
- `status.md`
- `COMPACTIFIED_CONTEXT.md`

Update as needed:

- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`
- an audit report file if the project keeps one

## Audit flow

1. Analyze the active specification and architecture.
2. Inventory the relevant repository surface area.
3. Map each requirement to likely implementation points.
4. Verify implementation behavior and boundary discipline.
5. Classify gaps and violations by severity.
6. Record findings and recommend the next skill.

Partial audits are failure. Cover the full relevant repository.

## Companion skill integration

- `get-shit-done`: use as the normal entrypoint when project scope or planning still needs framing.
- `architect-planner`: use when the audit shows the architecture is underspecified or invalid.
- `long-running-development`: use for remediation after gaps are confirmed.
- `bug-hunter`: use when a finding depends on reproducing a failing behavior.
- `context-manager`: use to preserve audit findings and trim context before handoff.
- `orchestrator`: use when the audit should automatically trigger remediation loops.

## Completion criteria

- Requirements were enumerated.
- Relevant files were inspected.
- Coverage and violations were recorded.
- The next action is explicit in `status.md`.
```
