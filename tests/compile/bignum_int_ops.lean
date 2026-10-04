/-!
Big `Int`/`Nat` runtime arithmetic: `Int` division and modulus for all sign
combinations, conversions from big `Int`s to `Nat`s around the scalar/bignum
boundaries, division by zero, `Nat.powMod`, shifts, and operations whose two
operands are the same object.

Every operand is computed at run time (`z` is a run-time zero), so the big
values are fresh heap objects and nothing is constant-folded. The expected
output was computed independently with Python's integers.
-/

@[noinline] def pow2 (k : Nat) : Nat := 2 ^ k

def check (name : String) (b : Bool) : IO Unit :=
  unless b do IO.println s!"FAILED: {name}"

/-- Every `Int` division/modulus operation on `a` and `b`. -/
def divmods (a b : Int) : String :=
  s!"{a} {b}: {a / b} {a % b} {a.tdiv b} {a.tmod b} {a.fdiv b} {a.fmod b}"

def main : IO Unit := do
  let z := (← IO.monoNanosNow) * 0
  let p (k : Nat) : Nat := pow2 (k + z)
  let pi (k : Nat) : Int := Int.ofNat (p k)

  -- `Int` division and modulus, all sign combinations, incl. by zero and by ±1
  let as : List Int := [pi 100 + 12345, pi 64 + 1, pi 63, pi 31, 7, 0]
  let bs : List Int := [pi 70 + 3, pi 64 + 1, pi 31, 3, 1, 0]
  for a in as ++ (as.filter (· != 0)).map (- ·) do
    for b in bs ++ (bs.filter (· != 0)).map (- ·) do
      IO.println (divmods a b)
  -- balanced division and modulus
  for a in as ++ (as.filter (· != 0)).map (- ·) do
    let ms : List Nat := [p 70 + 3, p 64 + 1, p 31, 3, 0]
    IO.println s!"bmod/bdiv {a}: {ms.map (fun m => (a.bmod m, a.bdiv m))}"

  -- big `Int`s that become scalar or big `Nat`s, approached from both sides
  -- (`LEAN_MAX_SMALL_NAT` is `2^63 - 1` on 64-bit platforms)
  let vs : List (Nat × Int) := [
    (p 31 - 1, pi 31 - 1), (p 31, pi 31), (p 31 + 1, pi 31 + 1), (p 32, pi 32),
    (p 62, pi 62), (p 63 - 2, pi 63 - 2), (p 63 - 1, pi 63 - 1), (p 63, pi 63),
    (p 63 + 1, pi 63 + 1), (p 64 - 1, pi 64 - 1), (p 64, pi 64), (p 100, pi 100),
    -- the same values, computed from above and below
    (p 63 - 1, pi 64 - pi 63 - 1), (p 63 - 1, (pi 62 - 1) * 2 + 1),
    (p 63, pi 64 - pi 63), (p 31, pi 32 - pi 31), (p 31, (pi 31 - 1) + 1)]
  for (n, v) in vs do
    check s!"toNat {v}" (v.toNat == n && (-v).toNat == 0)
    check s!"natAbs {v}" (v.natAbs == n && (-v).natAbs == n)
    check s!"fresh natAbs {v}" ((v * 2).natAbs == 2 * n && (-(v * 2)).natAbs == 2 * n)
    check s!"natAbs neg sub {v}" ((-v - 1).natAbs == n + 1)
    check s!"Int.toNat result is usable {v}" (v.toNat + 1 - 1 == n && v.toNat * 3 / 3 == n)
    check s!"Int unchanged {v}" (v == Int.ofNat n)
    IO.println s!"{v} {v.toNat} {(-v).natAbs} {(-v - 1).natAbs} {(v - 1).toNat}"

  -- `Nat` division and modulus by zero, `powMod`
  let a := p 200 - 1 - p 70
  let b := p 150 + 12345
  IO.println s!"div0 {a / 0} {a % 0} {(a : Int) / 0} {(-(a : Int)) % 0} {(-(a : Int)).tdiv 0} {(-(a : Int)).tmod 0}"
  IO.println s!"powMod {Nat.powMod a b 1} {Nat.powMod a 0 1} {Nat.powMod a 0 b} {Nat.powMod a 1 0 == a} {Nat.powMod 0 b a} {Nat.powMod a 2 b} {Nat.powMod a b (p 64 + 13)} {Nat.powMod 3 a (p 61 - 1)}"

  -- shifts by 0, by large amounts, with tiny results
  IO.println s!"shift {a <<< 0 == a} {a >>> 0 == a} {a >>> 199} {a >>> 200} {a >>> (p 40)} {a >>> (p 64)} {a >>> (p 100)}"
  IO.println s!"shift {(a <<< 64) >>> 64 == a} {(a <<< 1000) >>> 1190} {0 <<< (p 40)} {p 64 >>> 1} {p 64 >>> 64} {p 64 >>> 65}"

  -- the same object as both operands
  IO.println s!"self {a + a == 2 * a} {a - a} {a * a == a ^ 2} {a / a} {a % a} {a &&& a == a} {a ||| a == a} {a ^^^ a} {Nat.gcd a a == a} {Nat.powMod a a a}"
  let x : Int := -(b : Int)
  IO.println s!"self {x + x == 2 * x} {x - x} {x * x == (b * b : Nat)} {x / x} {x % x} {x.tdiv x} {x.tmod x} {x.fdiv x} {x.fmod x} {x.bmod x.natAbs}"

  check "operands unchanged" (a == p 200 - 1 - p 70 && b == p 150 + 12345 && x == -(b : Int))
  IO.println "done"
