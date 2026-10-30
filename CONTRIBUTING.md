# Contributing

Every code change must be documented so that maintainers and users can understand what changed without reverse-engineering the diff.

## Required documentation

Whenever `twitch-helper.user.js` changes, add an entry to `CHANGELOG.md` in the same pull request or commit. Do not submit an undocumented userscript change.

Each entry must describe:

1. **What changed:** the behavior users will notice, not just an implementation detail.
2. **Where it changed:** the affected functions, UI sections, settings, or files.
3. **Why it changed:** the bug, limitation, or requested behavior being addressed.
4. **Compatibility:** whether stored settings, sync data, browser behavior, or existing workflows are affected; document migrations when applicable.
5. **Verification:** the checks actually performed, including browser/version and reproduction steps where relevant. Never claim a test passed if it was not run.

## Pull requests

- Use the repository pull-request template.
- Keep each pull request focused. Call out unrelated behavior changes explicitly rather than hiding them in a bug fix.
- Include before/after behavior and concise reproduction steps for user-facing fixes.
- Mention performance and memory implications for media-preview, caching, and conversion changes.
- For changes that affect exports, list the input media type, output format, and settings used in testing.
- Update `CHANGELOG.md` in the same pull request as the code change. The Changelog Requirement workflow checks this for changes to `twitch-helper.user.js`.

## Commit messages

Use a version and area in the subject, for example:

`[5.9.81] Preview: coalesce timeline seeks`

Add a commit body for non-trivial changes. The body should state the cause, the approach, relevant functions/files, and verification performed. A vague message such as `fix`, `update`, or `changes` is not sufficient.

## Safe changes

- Preserve existing gallery, upload, synchronization, and conversion behavior unless the task explicitly requires changing it.
- Avoid embedding credentials or personal tokens in code, tests, issues, or changelog entries.
- Bound caches and release resources such as `ImageBitmap`, object URLs, timers, event listeners, and workers when an editor session closes.
- Prefer small, testable changes and explain any browser-specific assumptions.