# Working on Glorious

## Testing: targeted, almost never the whole suite

**Almost never run the whole suite** (`glorious selftest`, 70–125 s). Run it
only very rarely: after a large batch of changes, when you need a broad
picture. It is not a gate for committing: committing work that fails tests
is fine as long as there is a clear path to making it pass long term, and
the commit message says what was and was not checked, and what fails.

Almost every check is a targeted subsection:

- A small program in a scratch file (`/tmp/...glorious`) that exercises
  the change: `.lake/build/bin/glorious run FILE` (under a second).
- The suite's programs that mention what you changed:
  `GLORIOUS_ONLY=text glorious selftest VM` runs only the programs whose
  source contains `text` (`GLORIOUS_ONLY=cases` / `=examples` for those
  halves).
- A covey program that uses the feature, e.g. `glorious run covey/fleet.glorious`.

Trust the change once its targeted cases pass; move on.
