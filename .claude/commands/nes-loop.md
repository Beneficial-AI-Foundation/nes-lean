---
description: One tick of the autonomous nes-lean build loop. Run under /loop. Works through PLAN.md milestone by milestone, a batch of independent checklist items per tick (fanned out to subagents), state in PROGRESS.md, one stacked PR per milestone. Does not stop until M7 is ready for review.
---

You are one tick of a long-running autonomous loop building the formally verified NES
emulator in this repo. The user is away. PROGRESS.md is the only memory that survives
between ticks and across context compaction — treat it as the program counter.

## Invariants (never violate)

- Follow PLAN.md as written, including the §10 decisions. No scope changes; if the plan is
  wrong, record it under "Decisions log" in PROGRESS.md with the fix, then apply the fix.
- One milestone = one PR, stacked: branch `m<k>-…` from the previous milestone branch, PR
  base = that branch (M0 → `main`). The PR is opened as a **draft at milestone start**,
  every commit is pushed to it as it lands, and it is marked **ready for review only at
  milestone close**. Never merge a PR. Never push to `main`.
- The only permitted force push is `--force-with-lease` on the *current milestone branch*
  right after rebasing the stack because its base was merged.
- No `sorry`, no `native_decide`, no `partial`/`unsafe`/`panic!`/`IO` under `Nes/`.
- The product is the native binary from Lean's C backend. Code on the emulation hot path
  follows PLAN.md §4 "Performance (compiled C)": `UInt*` scalars, no `Nat`/`Int`/closures/
  `List`/`Option` allocation in `stepCycle`, uniquely-referenced `Vector` updates.
  Benchmarks are taken on the `-O3` native binary, never via `#eval`.
- No commercial ROMs in the repo; test data only via `scripts/fetch-testdata.sh`.
- End every commit message with the attribution line your session's instructions specify.
- Keep context small: never `cat` large files or print full build logs. Use `grep -n`,
  `tail -40`, `lake build 2>&1 | grep -E "error|warning: declaration uses 'sorry'" | head`.
  Send wide searches and open-ended proof exploration to a subagent; keep its brief tight.

## Tick procedure

1. **Orient** (cheap). Read PROGRESS.md in full. Run `git status -sb` and `git branch
   --show-current`. If you are not on the current milestone branch, check it out. Read only
   the PLAN.md section the next item needs (`grep -n` to locate it).

   **Milestone start** — if the current milestone's branch does not exist yet, before any
   other work: create it from its base; set "Current branch" in PROGRESS.md; commit that as
   `M<k>: start milestone`; `git push -u origin <branch>`; open the PR immediately as a
   draft so every later commit lands on it:
   `gh pr create --draft --base <base> --title "M<k>: <title>" --body-file -` with a body
   that holds the milestone's checklist copied from PROGRESS.md; record the PR number in
   the table (status "in progress"). The PR exists before the first line of code.

2. **Housekeeping** (cheap, before new work).
   - If the current milestone has a PR: `gh pr checks <n>` and `gh pr view <n> --comments`.
     A red check or an unaddressed review comment is this tick's work — fix, push, done.
   - If the previous milestone's PR was merged: `git fetch`, `git rebase --onto main
     <old-base> <branch>`, push with `--force-with-lease`, `gh pr edit <n> --base main`,
     update the PR table.
   - If a background build/test you started last tick finished, act on its result first.

3. **Pick a batch.** Take the first unchecked item of the current milestone (or the "Next
   action" line if it is more specific), then add every other unchecked item of the same
   milestone that is *independent* of it and of each other, up to 4 items. Independent
   means: disjoint files, and neither item needs the other's output (a proof needs its
   definitions, a test needs the code it tests, "PR ready" is always last). The "Parallel
   tracks" line under each milestone in PROGRESS.md says what the plan expects to run side
   by side; the checklist order is otherwise a suggestion, not a dependency. Never start the
   next milestone while the current one has unchecked items.

4. **Fan out and do.** One item → do it yourself. Two or more → spawn one subagent per
   item with the `Agent` tool, all in a single message so they run concurrently, and wait
   for all of them; do not duplicate their work meanwhile. Each brief must contain: the
   item text, the PLAN.md section it implements (quote the section, the agent has no
   context), the invariants above, the exact files it owns, and these rules: touch only
   those files, do not edit PROGRESS.md / `Nes.lean` / `lakefile.toml` / CI, do not commit,
   run `lake build <its modules>` before reporting, and report a ≤10-line summary ending
   with the list of files changed and any gotcha learned. Shared files (`Nes.lean` import
   list, `lakefile.toml`, PROGRESS.md, CI) are edited only by you, after the agents return.
   Open-ended proof search is also a good subagent job even for a single item: give it the
   theorem statement and a 3-attempt budget, keep the main context clean.
   Long builds/tests: run with a 10-minute timeout, or start them in the background and end
   the tick — the completion notification wakes you.
   - Proof items: attempt budget of 3 ticks per theorem. After that, split it into lemmas
     with their own checklist lines, or move it to "Deferred theorems" with the blocker —
     unless it is the milestone's headline theorem (T-REF-1 for M2, T-PPU-6 for M6), which
     cannot be deferred.
   - Spec-vs-hardware mismatches found by tests: fix the spec, and record the hardware fact
     as a gotcha.

5. **Verify the integration yourself**: after the agents return, `lake build` of every
   touched module together (agents only built their own); run the tests the items name;
   `grep -rn "sorry" Nes/` must be empty before committing closed work. A subagent's
   report is a claim, not proof — check its diff before ticking its item.

6. **Record** in PROGRESS.md, in this order: tick the checklist items; set "Next action";
   append gotchas (anything that cost more than one attempt: Lean API names, tactic
   behaviour, Lake/CI quirks, hardware facts that contradicted the docs — including the
   ones the subagents reported); append one tick-log line and trim the log to 20 lines;
   update benchmarks/deferred theorems if relevant. Then commit — one commit per item,
   staging that item's files, message `M<k>: <what>`; PROGRESS.md goes in the last commit
   of the tick — and push to the milestone branch after every commit, so each one shows up
   on the draft PR as it lands. Finally refresh the PR body with the milestone's current
   checklist (`gh pr edit <n> --body-file -`) so progress is readable on GitHub without
   opening the repo. (Safety net: if the milestone somehow has no PR, open the draft now as
   in step 1.)

7. **Milestone close** — when the last item is ticked, check the definition of done in
   PROGRESS.md (build, tests, no sorry, axiom registry, headline theorems closed). If it
   holds: write the final PR body (what was built, theorems closed, theorems deferred,
   benchmarks, the ticked checklist), `gh pr ready <n>`, mark the row "ready for review".
   Then start the next milestone right away: set "Current milestone"/"Next action", and
   run the milestone-start steps from step 1 (branch from this one, bootstrap commit,
   push, draft PR). If the definition of done does not hold, add the missing work as
   checklist items instead and stay on this milestone.

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
