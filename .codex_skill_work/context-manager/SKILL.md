---
name: context-manager
description: Maintains durable project memory, compacts context, and restores the current project state for long-running Codex sessions. Companion skill in the get-shit-done stack.
metadata:
  short-description: Keep project memory stable across long runs
---

```md
# Context Manager Skill

This skill prevents context drift during long-running work.
It keeps the canonical project memory current so the rest of the stack can resume quickly and safely.

## When to trigger this skill

- Before a long autonomous run
- After a noisy audit, debugging session, or milestone burst
- When `COMPACTIFIED_CONTEXT.md` is stale
- When a handoff between skills or sessions would otherwise lose state

## Canonical project memory

This skill maintains:

- `spec.md`
- `architecture.md`
- `plan.md`
- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`

If the project uses `.planning/`, preserve the same structure there.

## Core workflow

1. Read the current canonical files and recent evidence.
2. Remove duplication and stale assumptions.
3. Summarize the current truth into `COMPACTIFIED_CONTEXT.md`.
4. Ensure `status.md` names the current phase, next step, and next skill.
5. Preserve unresolved questions instead of hiding them.

## Companion skill integration

- `get-shit-done`: normal entrypoint and canonical format owner.
- `architect-planner`: use after context normalization when architecture must be designed or revised.
- `repo-auditor`: use after summarization when spec compliance needs checking.
- `long-running-development`: use after summarization when milestones are ready to execute.
- `bug-hunter`: use after summarization when there is an active failing behavior.
- `orchestrator`: upstream or downstream controller that decides which worker should run next.

## Completion criteria

- Canonical files are internally consistent.
- `COMPACTIFIED_CONTEXT.md` reflects the current truth.
- The next skill and next checkpoint are explicit.
```
