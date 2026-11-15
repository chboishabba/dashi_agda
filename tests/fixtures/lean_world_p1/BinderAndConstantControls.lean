/-!
Source-written P1 positive/negative controls. Actual Lean 4.28 compilation
and native-v3 elaboration receipts are still required before claiming success.
Binder display names do not alter the elaborated proposition. Changed numeral
and RHS constructors do. No sorry, axioms, or unrelated synthetic proof.
-/
namespace DASHIP1

theorem first (x : Nat) : x + 0 = x := Nat.add_zero x
theorem second (n : Nat) : n + 0 = n := Nat.add_zero n
theorem changed (n : Nat) : n + 1 = Nat.succ n := Nat.add_one n

end DASHIP1
