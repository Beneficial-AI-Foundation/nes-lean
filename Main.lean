import Nes

/-- Headless CLI entry point (PLAN.md §5.6). Filled in from M3 onward. -/
def main (args : List String) : IO UInt32 := do
  IO.println s!"nes-lean: no emulator yet (args: {args})"
  return 0
