import Ragu.Fingerprint.Instances

/-- Entry point of `lake exe fingerprints`.

Prints `<module name> <digest>` for every exported formal instance, computed
from the `Clean` reimplementation. CI compares this output against
`cargo run -p lean_extraction -- fingerprint`. -/
def main : IO UInt32 := do
  let mut failed := false
  for (name, inst) in Ragu.Fingerprint.instances do
    match inst.fingerprint with
    | .ok digest => IO.println s!"{name} {digest}"
    | .error err =>
      IO.eprintln s!"error: {name}: {err}"
      failed := true
  return if failed then 1 else 0
