---
name: architect-planner
description: Designs architecture and milestone plans before coding. Companion skill in the get-shit-done autonomous development stack.
metadata:
  short-description: Design architecture before implementation
---

```md
# Architect Planner Skill

This skill stabilizes architecture before code changes begin.
It is normally invoked from `get-shit-done`, which defines the canonical project files and status format.

## When to trigger this skill

- A large feature or subsystem must be designed before implementation.
- Existing plans are too vague to support execution.
- Module boundaries or data flow are unclear.
- `get-shit-done` has identified architecture as the next checkpoint.

## Canonical inputs and outputs

Read first:

- `spec.md`
- `architecture.md` if it exists
- `plan.md`
- `status.md`
- `COMPACTIFIED_CONTEXT.md`

Update as needed:

- `architecture.md`
- `plan.md`
- `status.md`
- `COMPACTIFIED_CONTEXT.md`

Follow the file conventions established by `get-shit-done`.

## Core workflow

1. Analyze the problem and extract requirements.
2. Inspect the repository architecture and existing integration points.
3. Design module boundaries, dependency direction, and data flow.
4. Translate the architecture into small verifiable milestones.
5. Record key risks and mitigations.
6. Hand off execution to `long-running-development`.

This skill plans. It does not act as the main implementation loop.

## Companion skill integration

- `get-shit-done`: normal entrypoint; use it first when project state is still forming.
- `context-manager`: use before or after planning if project memory is stale or oversized.
- `repo-auditor`: use after planning when you need to verify the repo against the new design.
- `long-running-development`: primary downstream consumer of the milestones produced here.
- `bug-hunter`: use if planning surfaces a defect that must be reproduced before design can continue.
- `orchestrator`: use when the project should repeatedly cycle through planning, execution, audit, and repair.

## Completion criteria

- Architecture is documented.
- Module boundaries and data flow are explicit.
- Milestone plan is small enough to execute safely.
- Risks are recorded.
- `status.md` identifies `long-running-development` or `repo-auditor` as the next skill.
```
