/-
# Day 2 seminar: types, functions, and induction

Replace each `sorry` with a proof.  Sections follow the lecture, and within a
section the exercises go from routine to harder.  The definitions come from
`Cyprus.Day2Lecture`; do not redefine them.  The Collatz section is for anyone
who finishes early.
-/

import Cyprus.Day1Lecture
import Cyprus.Day2Lecture
import Mathlib.Tactic

namespace Cyprus.Day2Seminar

open Cyprus.Islanders Cyprus.Day2Lecture Cyprus.Day1Lecture

section InductiveTypes

theorem flip_knave : Role.flip .knave = .knight :=
sorry

theorem flip_eq_knight_iff (r : Role) : r.flip = .knight ↔ r = .knave :=
sorry

open MyNat in
theorem succ_add (n m : MyNat) : add (.succ n) m = .succ (add n m) :=
sorry

open MyNat in
theorem add_comm (n m : MyNat) : add n m = add m n :=
sorry

/-- The same proof as `MyNat.zero_add`, now for `Nat`.  Use `Nat.add_succ`, not `omega` or `simp`. -/
theorem nat_zero_add (n : Nat) : 0 + n = n :=
sorry

end InductiveTypes

section Functions

variable {α β γ : Type}

theorem surjective_id : Surjective (fun x : α => x) :=
sorry

theorem flip_injective : Injective Role.flip :=
sorry

theorem double_add (n m : Nat) : double (n + m) = double n + double m :=
sorry

theorem half_double_add_one (n : Nat) : half (double n + 1) = n :=
sorry

/-- `half` has a left inverse, but it is not injective. -/
theorem half_not_injective : ¬Injective half :=
sorry

theorem surjective_comp {f : α → β} {g : β → γ} (hf : Surjective f) (hg : Surjective g) :
    Surjective (fun x => g (f x)) :=
sorry

theorem injective_of_comp_injective (f : α → β) (g : β → γ)
    (h : Injective (fun x => g (f x))) : Injective f :=
sorry

/-- A function with a right inverse is surjective. -/
theorem surjective_of_rightInverse {f : α → β} {g : β → α} (h : ∀ y, f (g y) = y) :
    Surjective f :=
sorry

/-- Every function out of `Role` that is injective is also surjective. -/
theorem role_surjective_of_injective (f : Role → Role) (hf : Injective f) : Surjective f :=
sorry

end Functions

section InductivePredicates

theorem myEven_add {n m : Nat} (hn : MyEven n) (hm : MyEven m) : MyEven (n + m) :=
sorry

theorem double_half_of_myEven {n : Nat} (h : MyEven n) : double (half n) = n :=
sorry

theorem not_myEven_double_add_one (n : Nat) : ¬MyEven (double n + 1) :=
sorry

/-- Every number is either `double k` or `double k + 1`. -/
theorem double_or_double_add_one (n : Nat) : ∃ k, n = double k ∨ n = double k + 1 :=
sorry

theorem myLe_zero (n : Nat) : MyLe 0 n :=
sorry

theorem myLe_succ_succ {n m : Nat} (h : MyLe n m) : MyLe (n + 1) (m + 1) :=
sorry

theorem myLe_double (n : Nat) : MyLe n (double n) :=
sorry

theorem myLe_iff_exists_add (n m : Nat) : MyLe n m ↔ ∃ k, n + k = m :=
sorry

end InductivePredicates

section Decidable

theorem isEven_double (n : Nat) : isEven (double n) = true :=
sorry

/-- A Boolean equality test on `Nat`. -/
def isEq : Nat → Nat → Bool
  | 0, 0 => true
  | _ + 1, 0 => false
  | 0, _ + 1 => false
  | n + 1, m + 1 => isEq n m

example : isEq 3 3 = true := rfl

theorem isEq_sound (n m : Nat) : isEq n m = true → n = m :=
sorry

theorem isEq_complete (n : Nat) : isEq n n = true :=
sorry

end Decidable

section Collatz

theorem collatzStep_double (n : Nat) : collatzStep (double n) = n :=
sorry

/-- Follow 6 down to 1 by hand. -/
theorem collatzFinite_six : CollatzFinite 6 :=
sorry

theorem collatzFinite_double {n : Nat} (h : CollatzFinite n) : CollatzFinite (double n) :=
sorry

end Collatz

end Cyprus.Day2Seminar
