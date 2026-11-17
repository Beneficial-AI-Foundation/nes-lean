---
description: One tick of the autonomous nes-lean build loop. Run under /loop. Works through PLAN.md milestone by milestone, one checklist item per tick, state in PROGRESS.md, one stacked PR per milestone. Does not stop until M7 is ready for review.
---

You are one tick of a long-running autonomous loop building the formally verified NES
emulator in this repo. The user is away. PROGRESS.md is the only memory that survives
between ticks and across context compaction — treat it as the program counter.

## Invariants (never violate)

- Follow PLAN.md as written, including the §10 decisions. No scope changes; if the plan is
  wrong, record it under "Decisions log" in PROGRESS.md with the fix, then apply the fix.
- One milestone = one PR, stacked: branch `m<k>-…` from the previous milestone branch, PR
  base = that branch (M0 → `main`). Never merge a PR. Never push to `main`.
- The only permitted force push is `--force-with-lease` on the *current milestone branch*
  right after rebasing the stack because its base was merged.
- No `sorry`, no `native_decide`, no `partial`/`unsafe`/`panic!`/`IO` under `Nes/`.
- No commercial ROMs in the repo; test data only via `scripts/fetch-testdata.sh`.
- End every commit message with the attribution line your session's instructions specify.
- Keep context small: never `cat` large files or print full build logs. Use `grep -n`,
  `tail -40`, `lake build 2>&1 | grep -E "error|warning: declaration uses 'sorry'" | head`.
  Send wide searches and open-ended proof exploration to a subagent; keep its brief tight.

## Tick procedure

1. **Orient** (cheap). Read PROGRESS.md in full. Run `git status -sb` and `git branch
   --show-current`. If you are not on the current milestone branch, check it out (create it
   from its base if it does not exist yet). Read only the PLAN.md section the next item
   needs (`grep -n` to locate it).

2. **Housekeeping** (cheap, before new work).
   - If the current milestone has a PR: `gh pr checks <n>` and `gh pr view <n> --comments`.
     A red check or an unaddressed review comment is this tick's work — fix, push, done.
   - If the previous milestone's PR was merged: `git fetch`, `git rebase --onto main
     <old-base> <branch>`, push with `--force-with-lease`, `gh pr edit <n> --base main`,
     update the PR table.
   - If a background build/test you started last tick finished, act on its result first.

3. **Pick** the first unchecked item of the current milestone (or the "Next action" line if
   it is more specific). Never start the next milestone while the current one has unchecked
   items.

4. **Do** exactly that item. Budget: one item per tick. Long builds/tests: run with a
   10-minute timeout, or start them in the background and end the tick — the completion
   notification wakes you.
   - Proof items: attempt budget of 3 ticks per theorem. After that, split it into lemmas
     with their own checklist lines, or move it to "Deferred theorems" with the blocker —
     unless it is the milestone's headline theorem (T-REF-1 for M2, T-PPU-6 for M6), which
     cannot be deferred.
   - Spec-vs-hardware mismatches found by tests: fix the spec, and record the hardware fact
     as a gotcha.

5. **Verify**: `lake build` for touched modules; run the tests the item names; `grep -rn
   "sorry" Nes/` must be empty before committing closed work.

6. **Record** in PROGRESS.md, in this order: tick the checklist item; set "Next action";
   append gotchas (anything that cost more than one attempt: Lean API names, tactic
   behaviour, Lake/CI quirks, hardware facts that contradicted the docs); append one tick-log
   line and trim the log to 20 lines; update benchmarks/deferred theorems if relevant.
   Then commit (one commit per item, message `M<k>: <what>`), and `git push -u origin
   <branch>`. If this milestone has no PR yet, open one now as a draft:
   `gh pr create --draft --base <base> --title "M<k>: <title>" --body-file -` and record the
   number in the table.

7. **Milestone close** — when the last item is ticked, check the definition of done in
   PROGRESS.md (build, tests, no sorry, axiom registry, headline theorems closed). If it
   holds: write the PR body (what was built, theorems closed, theorems deferred,
   benchmarks), `gh pr ready <n>`, mark the row "ready for review", create the next
   milestone branch from this one, set "Current milestone"/"Current branch"/"Next action",
   commit and push. If it does not hold, add the missing work as checklist items instead.

8. **Blocked?** If progress needs the user (auth failure, a decision the plan does not
   cover, a dependency that cannot be fetched), set "Blocked: yes — <why> — <what the user
   should do>" in PROGRESS.md, commit, and keep the loop alive at a slow heartbeat; do the
   first unblocked item of the milestone meanwhile if one exists.

9. **Schedule the next tick** as the last action of the turn. Write one visible line
   (milestone, what this tick did, next action), then call `ScheduleWakeup` with
   `prompt: "/nes-loop"`, `delaySeconds: 60` (the minimum; use 1800 only while blocked),
   `noop: false` if anything changed, and a one-sentence `reason`. Call it with
   `stop: true` only when the M7 row reads "ready for review" — that is the only normal
   ending of this loop. Then state the final outcome in one paragraph.
