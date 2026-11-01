# GitHub Actions philosophy

CI is a shared resource, not an unlimited event sink. The repository's default
automation mindset is:

- Prefer the newest meaningful revision. Workflows share one repository-wide
  concurrency group per ref, so a newer run cancels stale queued or running
  work across the workflow fan-out.
- Trigger narrowly. Use `paths`, branch filters, and explicit event types when
  they express the workflow's real scope. Avoid running both `push` and
  `pull_request` validation for the same feature-branch update unless both are
  genuinely needed.
- Keep feature-branch validation on the pull request surface where possible;
  reserve automatic push validation for the default branch or other deliberate
  release lanes.
- Make expensive or exploratory work manual (`workflow_dispatch`) when it does
  not need to be a required PR check.
- Treat runner capacity and GitHub rate limits as design constraints. A green
  check is useful only if the repository can reach it predictably.

The standard repository-wide policy is:

```yaml
concurrency:
  group: dashi-global-${{ github.ref }}
  cancel-in-progress: true
```

When adding a workflow, start with the narrowest event and path filters that
match its purpose, then add broader triggers only when there is a concrete
consumer for them.
