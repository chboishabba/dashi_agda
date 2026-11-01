---
name: long-running-development
description: Executes large coding tasks autonomously using a structured plan → implement → validate → repair → repeat loop. Companion skill in the get-shit-done stack.
metadata:
  short-description: Long-horizon milestone execution loop
---

```md
# Long-Running Development Skill

This skill executes milestone-based implementation work without stopping after partial progress.
It should usually be entered from `get-shit-done` after planning is stable, often through `architect-planner`.

## Canonical project memory

Read before acting:

- `spec.md`
- `architecture.md`
- `plan.md`
- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`

Update during execution:

- `plan.md`
- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`

Use the document structure and checkpoint language defined by `get-shit-done`.

## Operating loop

1. Select the first incomplete milestone from `plan.md`.
2. Implement only the current milestone.
3. Run the milestone validation commands.
4. Repair failures until validation succeeds.
5. Mark the milestone complete in `status.md` and `devlog.md`.
6. Continue to the next milestone until no milestones remain.

Avoid unnecessary replanning. Re-enter `architect-planner` only when the plan has become invalid.

## Companion skill integration

- `get-shit-done`: canonical entrypoint and project format owner.
- `architect-planner`: upstream planner for milestones and architecture.
- `repo-auditor`: use before implementation to confirm coverage, or after implementation to verify alignment.
- `bug-hunter`: use immediately when reproduction or diagnosis is required beyond normal repair.
- `context-manager`: use to compact progress before long sessions or agent handoffs.
- `orchestrator`: use when repeated autonomous skill selection is required across many milestones.

## Definition of done

The task is complete only when:

- all planned milestones are complete
- validation commands succeed
- implementation matches the active specification
- unresolved TODOs blocking the scope are cleared or documented
- `status.md` reflects the finished state
```
