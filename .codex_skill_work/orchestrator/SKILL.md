---
name: orchestrator
description: Selects the next skill in the get-shit-done autonomous development stack based on project state, then repeats until the current objective is complete.
metadata:
  short-description: Lightweight controller for multi-skill autonomous runs
---

```md
# Orchestrator Skill

This skill is the lightweight controller for the autonomous development stack.
It decides which specialized skill should run next based on the canonical project state maintained by `get-shit-done` and `context-manager`.

## Core principle

Keep orchestration simple:

- read canonical state
- choose one next skill
- run one bounded step
- update state
- repeat

Do not build an overly clever planner inside this skill.

## Canonical state sources

Read:

- `spec.md`
- `architecture.md`
- `plan.md`
- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`

Update:

- `status.md`
- `devlog.md`
- `COMPACTIFIED_CONTEXT.md`

## Default decision logic

- If project memory is stale or fragmented, run `context-manager`.
- If architecture is missing or invalid, run `architect-planner`.
- If implementation alignment is unknown, run `repo-auditor`.
- If milestones remain and no active defect blocks progress, run `long-running-development`.
- If tests or runtime behavior fail, run `bug-hunter`.
- If scope itself is unclear, bounce back to `get-shit-done`.

## Companion skill integration

- `get-shit-done`: canonical entrypoint and format owner; use it when state framing is weak.
- `context-manager`: maintain durable state between orchestration cycles.
- `architect-planner`: produce architecture and milestone structure.
- `repo-auditor`: verify repo alignment against spec and architecture.
- `long-running-development`: execute milestone work.
- `bug-hunter`: resolve failures discovered during execution or audit.

## Completion criteria

- The current objective is complete, or
- The next required skill is clearly identified and recorded, or
- A hard blocker is documented with evidence.
```
