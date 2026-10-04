/-!
Big `Nat`/`Int` arithmetic in the runtime, including results that cross the
scalar/bignum boundary in either direction and operations whose big operands
must not be modified (the runtime computes results into fresh `mpz` values).
-/

@[noinline] def pow2 (k : Nat) : Nat := 2 ^ k

def check (name : String) (b : Bool) : IO Unit :=
  unless b do IO.println s!"FAILED: {name}"

def main : IO Unit := do
  let a := pow2 200 - 1 - pow2 70
  let b := pow2 150 + 12345
  let c := pow2 64
  -- identities over big operands
  check "add/sub" ((a + b) - b == a)
  check "xor" ((a ^^^ b) ^^^ b == a)
  check "and/or/xor" ((a &&& b) ||| (a ^^^ b) == a ||| b)
  check "shift" ((a <<< 77) >>> 77 == a)
  check "divmod" (a / b * b + a % b == a)
  check "mul/div" (a * b / b == a)
  check "gcd" (Nat.gcd (a * 6) (b * 6) % 6 == 0)
  -- big results that become small, and the operands stay unchanged
  check "sub small" ((pow2 100 + 5) - pow2 100 == 5)
  check "sub zero" (a - a == 0)
  check "sub neg" (b - a == 0)
  check "xor self" (a ^^^ a == 0)
  check "xor small" (c ^^^ (c + 7) == 7)
  check "and small" (a &&& 0xff == 0xff)
  check "shiftr small" (pow2 200 >>> 198 == 4)
  check "shiftr zero" (a >>> 300 == 0)
  check "mod small" (a % 1000 == 951)
  check "div small" (a / pow2 190 == 1023)
  check "boundary" (c - 1 - (c - 2) == 1 && (c - 1) + 1 == c && (c + 1) - 2 == c - 1)
  check "succ" (a + 1 - a == 1)
  check "pow" (pow2 10 ^ 20 == pow2 200)
  check "powMod" (Nat.powMod a 3 b == a ^ 3 % b)
  check "operands unchanged" (a == pow2 200 - 1 - pow2 70 && b == pow2 150 + 12345)
  -- Int
  let x : Int := a
  let y : Int := -(b : Int)
  check "int add/sub" ((x + y) - y == x)
  check "int mul/ediv" (x * y / y == x)
  check "int emod" (x % y + y * (x / y) == x && 0 ≤ x % y)
  check "int tdiv/tmod" (x.tdiv y * y + x.tmod y == x)
  check "int neg" (-(-x) == x && -x + x == 0)
  check "int small" ((x + 3) - x == 3 && (y - 3) - y == -3)
  check "int boundary" (((2 : Int) ^ 31 - 1) + 1 == 2 ^ 31 && -((2 : Int) ^ 31) - 1 + 1 == -(2 ^ 31))
  check "int toNat" (x.toNat == a && y.toNat == 0 && (x - x + 5).toNat == 5)
  check "int toNat natAbs big" ((x * 2).toNat == 2 * a && (-(x * 2)).natAbs == 2 * a && y.natAbs == b)
  check "int operands unchanged" (x == (a : Int) && y == -(b : Int))
  IO.println s!"{a % 1000000007} {(a * b) % 1000000007} {(a ^^^ b) >>> 100} {(x * y) / (pow2 300 : Int)}"
  IO.println "done"
