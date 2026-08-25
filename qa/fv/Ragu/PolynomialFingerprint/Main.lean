import Ragu.Fingerprint.Instances
import Ragu.PolynomialFingerprint

/-- Print one `ragu-fv-polynomial-v1` TSV record per enrolled instance.

Usage: `lean --run Ragu/PolynomialFingerprint/Main.lean <seed-hex> <points>`. -/
def main (args : List String) : IO UInt32 :=
  match args with
  | [seedHex, pointsString] =>
      match pointsString.toNat? with
      | none => IO.eprintln s!"invalid point count: {pointsString}" *> pure 2
      | some points =>
          match Ragu.PolynomialFingerprint.parseSeed seedHex with
          | .error err => IO.eprintln s!"error: {err}" *> pure 2
          | .ok seed => do
              let mut failed := false
              for (name, inst) in Ragu.Fingerprint.instances do
                match inst.polynomialFingerprint name seed points with
                | .ok record => IO.println record
                | .error err =>
                  IO.eprintln s!"error: {name}: {err}"
                  failed := true
              return if failed then 1 else 0
  | _ =>
      IO.eprintln "usage: polynomial-fingerprints <64-hex-digit-seed> <points>" *> pure 2
