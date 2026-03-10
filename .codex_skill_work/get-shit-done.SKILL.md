---
name: get-shit-done
description: Comprehensive single-developer planning system with references, templates, and workflows for GSD-style projects. Default entrypoint for the autonomous development skill stack.
metadata:
  short-description: Planning system and canonical entrypoint for shipping work end-to-end
---

```md
# Gets Shit Done Planning System

This skill is the **default entrypoint** for the broader autonomous development stack.
Use it to establish the canonical project format, decide which companion skill should run next,
and keep planning, execution, and validation aligned.

## Companion skill stack

`get-shit-done` is the coordinator-facing entrypoint for:

- `architect-planner`
- `repo-auditor`
- `long-running-development`
- `bug-hunter`
- `context-manager`
- `orchestrator`
- `update-docs-todo-implement`

These skills may be called individually, but they should inherit the document structure,
phase language, and checkpoint discipline defined here.

## Canonical project memory

Prefer a consistent set of durable files:

- `spec.md` or `.planning/spec.md`
- `architecture.md` or `.planning/architecture.md`
- `plan.md` or `.planning/plan.md`
- `status.md` or `.planning/status.md`
- `devlog.md` or `.planning/devlog.md`
- `COMPACTIFIED_CONTEXT.md`

If only one location is practical, keep the files together. The exact directory is less important
than consistency.

All companion skills should:

- read existing project memory before acting
- preserve the canonical section structure where possible
- update the relevant state files before finishing

## When to trigger this skill

- You are starting a new project, phase, or milestone.
- You need to formalize intent before writing code.
- You need to decide which specialized skill should run next.
- You want to generate or update planning documents.
- You need a disciplined cadence for solo or small-team work.

This skill is **planning-first** and **routing-aware**.

## What this skill provides

- **References** (`references/`)
  - Planning principles
  - Research and execution pitfalls
  - Review and checkpoint heuristics
- **Templates** (`templates/`, `templates/codebase/`)
  - Phase plans
  - Milestone definitions
  - Design and research notes
- **Workflows** (`workflows/`)
  - Phase transitions
  - Milestone completion checks
  - Research → execution handoffs

Load only the files you need; do not eagerly read the entire skill.

## Core rules

- Planning precedes implementation.
- Documentation reflects intent *before* code exists.
- Every phase ends with an explicit checkpoint.
- If reality diverges from the plan, stop and update the plan.
- `get-shit-done` owns the canonical project format used by the companion skills.

## Default routing logic

After clarifying scope, route to the next appropriate skill:

- Use `context-manager` when project memory is missing, stale, or too large.
- Use `architect-planner` when architecture or milestone design is incomplete.
- Use `repo-auditor` when you must compare implementation against a spec or architecture.
- Use `long-running-development` when the task is approved for execution and milestones exist.
- Use `bug-hunter` when a failure must be reproduced, isolated, and fixed.
- Use `update-docs-todo-implement` when the documentation workflow itself must be enforced.
- Use `orchestrator` when the task needs repeated autonomous delegation across multiple phases.

## Typical workflow

1. **Clarify scope**
   - Identify whether the task is:
     - A new project
     - A new phase
     - A milestone within an existing phase
     - A debugging, audit, or orchestration problem
   - Select the appropriate template from `templates/`.

2. **Normalize project memory**
   - Ensure canonical files exist or identify the nearest equivalents.
   - Record assumptions, constraints, and success criteria.
   - Update `COMPACTIFIED_CONTEXT.md` with the current truth.

3. **Checkpoint before execution**
   - Confirm:
     - The goal is concrete
     - Inputs and outputs are defined
     - Failure modes are understood
     - The next skill is obvious
   - If unclear, do not proceed.

4. **Route to the specialized skill**
   - Hand off to the correct companion skill with the current canonical documents.

5. **Record outcomes**
   - Capture results, logs, or artifacts with timestamped filenames.
   - Note deviations from the plan.
   - Decide whether to:
     - Continue
     - Revise the plan
     - Close the milestone
     - Escalate to another companion skill

6. **Handoff to documentation workflow**
   - If docs, TODOs, or changelogs must change, explicitly invoke:
     - `update-docs-todo-implement`

## Output expectations

- One or more planning or state documents created or updated
- Clear statement of current phase or milestone
- Explicit next action or next skill
- List of assumptions and open questions

## Failure modes and exit conditions

Abort and report if:

- Goals remain ambiguous after planning
- Required inputs are missing
- Execution would violate stated constraints
- No valid next skill can be selected

Never power through confusion.

## Companion skill handoffs

- `architect-planner`: use after scope clarification when the architecture is not yet stable.
- `repo-auditor`: use when you need coverage or compliance against a specification.
- `long-running-development`: use after plan approval to execute milestone work.
- `bug-hunter`: use when validation fails or a defect must be reproduced.
- `context-manager`: use to compress or restore context before long runs.
- `orchestrator`: use to supervise repeated transitions among the other skills.

Each of those skills should reference this skill as the canonical entrypoint and format owner.
If they discover missing project structure, they should bounce back here or invoke `context-manager`.

## Notes

- This skill is intentionally opinionated.
- It is designed for momentum without chaos.
- Pair with `chat-context-sync` when plans depend on live ChatGPT conversations.
- Pair with `update-docs-todo-implement` when planning transitions into execution.

Maintain a `COMPACTIFIED_CONTEXT.md` summarizing key decisions for future maintainers.
```
