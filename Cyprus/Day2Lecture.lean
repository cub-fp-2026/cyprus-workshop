/-
# Day 2 lecture: types, functions, and induction

Running example: natural numbers, `double`, `half`, and `MyEven`.
-/

import Cyprus.Islanders
import Mathlib.Tactic

namespace Cyprus.Islanders.Role

inductive MyBool where
  | mytrue
  | myfalse

#print MyBool

def mynegate : MyBool → MyBool := fun b =>
  match b with
  | .mytrue => .myfalse
  | .myfalse => .mytrue

#print Role

def flip : Role → Role
  | .knight => .knave
  | .knave => .knight

end Cyprus.Islanders.Role

namespace Cyprus.Day2Lecture

open Cyprus.Islanders

section Roles

theorem flip_knight : Role.flip .knight = .knave := by
  rewrite [Role.flip]
  rfl

theorem flip_flip (r : Role) : r.flip.flip = r := by
  cases r <;> rfl

theorem flip_ne_self (r : Role) : r.flip ≠ r := by
  cases r
  · rw [Role.flip]
    trivial
  · rw [Role.flip]
    intro
    contradiction

end Roles

section Equality

variable {α β : Type}

inductive Eq (a : α) : α → Prop where
  | rfl : Eq a a

-- Equality: `rfl`, `rw`, and congruence.

theorem eq_symm {x y : α} (h : x = y) : y = x := by
  cases h
  rfl

theorem eq_trans {x y z : α} (hxy : x = y) (hyz : y = z) : x = z := by
  rw [hxy, hyz]

theorem congr_fun_arg (f : α → β) {x y : α} (h : x = y) : f x = f y := by
  congr

theorem congr_funfun_arg (f : α → α) {x y : α} (h : f x = f y) : f (f x) = f (f y) := by
  rw [h]

example {P : α → α → Prop} (h : ∀ a, P a a)
    : ∀ a b, Eq a b → P a b := by
  intro a b hab
  cases hab
  apply h

end Equality

section InductiveTypes

inductive MyNat where
  | zero
  | succ (n : MyNat)
  deriving DecidableEq, Repr

namespace MyNat

def add : MyNat → MyNat → MyNat
  | n, .zero => n
  | n, .succ m => .succ (add n m)

theorem add_zero (n : MyNat) : add n .zero = n := by
  rfl

-- n + (m + 1) = (n + m) + 1
theorem add_succ (n m : MyNat) : add n (.succ m) = .succ (add n m) := by
  rfl

theorem zero_add (n : MyNat) : add .zero n = n := by
  induction n
  · rfl
  · rewrite [add]
    congr

end MyNat

-- `Nat` has the same constructors; addition recurses on the right.
#print Nat

example (n : Nat) : n + 0 = n := rfl

example (n m : Nat) : n + (m + 1) = (n + m) + 1 := rfl

-- Constructors are injective and distinct.

theorem succ_inj {n m : Nat} (h : n + 1 = m + 1) : n = m := by
  injection h

theorem zero_ne_succ (n : Nat) : 0 ≠ n + 1 := by
  intro
  contradiction

end InductiveTypes

section Functions

variable {α β γ : Type}

def double : Nat → Nat
  | 0 => 0
  | n + 1 => double n + 2

def half : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => half n + 1

#eval double 5
#eval half 7

theorem double_eq_add_self (n : Nat) : double n = n + n := by
  induction n
  case zero => rfl
  case succ n' ih =>
    rw [double, ih]
    omega

theorem half_double (n : Nat) : half (double n) = n := by
  induction n <;> simp [double, half, *]

def Injective (f : α → β) : Prop := ∀ x y, f x = f y → x = y

def Surjective (f : α → β) : Prop := ∀ y, ∃ x, f x = y

theorem injective_id : Injective (fun x : α => x) := by
  unfold Injective
  intro x y h
  cases h
  rfl

theorem succ_injective : Injective Nat.succ := by
  intro x y h
  cases h
  rfl

theorem injective_of_leftInverse {f : α → β} {g : β → α} (h : ∀ x, g (f x) = x) :
    Injective f := by
  intro x y hxy
  calc x = g (f x) := by symm; apply h
       _ = g (f y) := by rw [hxy]
       _ = y := by apply h

theorem double_injective : Injective double := by
  intro n m hnm
  induction n generalizing m
  case zero =>
    cases m
    · rfl
    · rw [double] at hnm
      contradiction
  case succ n' ih =>
    cases m
    case zero =>
      repeat rw [double] at hnm
      contradiction
    case succ m' =>
      repeat rw [double] at hnm
      congr
      apply ih
      injection hnm
      rename_i hnm'
      injection hnm'

theorem half_surjective : Surjective half := by sorry

theorem injective_comp {f : α → β} {g : β → γ} (hf : Injective f) (hg : Injective g) :
    Injective (fun x => g (f x)) := by sorry

end Functions

section InductivePredicates

inductive MyEven : Nat → Prop where
  | zero : MyEven 0
  | add_two {n : Nat} : MyEven n → MyEven (n + 2)

inductive MyEven' : Nat → Prop where
  | pf (k : Nat) {n : Nat} : 2 * k = n → MyEven' n

example : MyEven 4 := by
  repeat constructor

example : MyEven' 4 := by
  apply MyEven'.pf 2
  rfl

theorem one_not_even : ¬MyEven 1 := by
  intro
  contradiction

example : ¬MyEven' 1 := by rintro ⟨(_ | _), h⟩ <;> simp at h

-- Induct on the number.
theorem myEven_double (n : Nat) : MyEven (double n) := by
  induction n <;> constructor
  assumption

-- Induct on the evidence of evenness.
theorem exists_double_of_myEven {n : Nat} (h : MyEven n) : ∃ k, double k = n := by
  induction h
  case zero =>
    exists 0
  case add_two n' h' ih =>
    obtain ⟨k, ih⟩ := ih
    exists k+1
    rw [double, ih]

theorem double_not_surjective : ¬Surjective double := by
  unfold Surjective
  intro h
  obtain ⟨x, h'⟩ := h 1
  have : MyEven 1 := by
    rw [← h']
    apply myEven_double
  apply one_not_even
  assumption

-- An inductive relation.

inductive MyLe : Nat → Nat → Prop where
  | refl (n : Nat) : MyLe n n
  | step {n m : Nat} : MyLe n m → MyLe n (m + 1)

example : MyLe 2 4 := by repeat constructor

theorem not_myLe_succ_zero (n : Nat) : ¬MyLe (n + 1) 0 := by
  intro h
  contradiction

theorem myLe_trans {n m k : Nat} (hnm : MyLe n m) (hmk : MyLe m k) : MyLe n k := by
  induction hmk
  case refl => assumption
  case step k' hmk' ih =>
    constructor
    assumption

example {n m k : Nat} (hnm : MyLe n m) (hmk : MyLe m k) : MyLe n k := by
  induction hnm generalizing k
  case refl => assumption
  case step m' hnm' ih => sorry -- painful

end InductivePredicates

section Decidable

def isEven : Nat → Bool
  | 0 => true
  | 1 => false
  | n + 2 => isEven n

-- Follow the recursion: 0, 1, and n + 2.
theorem isEven_sound : (n : Nat) → isEven n = true → MyEven n
| 0, h => by constructor
| 1, h => by contradiction
| n + 2, h => by
  constructor
  apply isEven_sound n
  rw [isEven] at h
  assumption

theorem isEven_complete {n : Nat} (h : MyEven n) : isEven n = true := by
  induction h
  · rfl
  · rw [isEven]
    assumption

-- Soundness and completeness turn the Boolean test into a decision procedure.
instance : DecidablePred MyEven := fun n =>
  decidable_of_iff (isEven n = true) ⟨isEven_sound n, isEven_complete⟩

example : MyEven 10 := by decide

example : ¬MyEven 7 := by decide

end Decidable

section Collatz

macro "сорян" : tactic => `(tactic| sorry)
macro "сорян" : term => `(sorry)

def collatzStep (n : Nat) : Nat :=
  if MyEven n then half n else 3 * n + 1

inductive CollatzFinite : Nat → Prop where
  | zero : CollatzFinite 0
  | one : CollatzFinite 1
  | step {n : Nat} : CollatzFinite (collatzStep n) → CollatzFinite n

def CollatzConjecture : Prop := ∀ n, CollatzFinite n

theorem half_le (n : Nat) : half n ≤ n := by
  induction n using half.induct <;> simp [half]; omega

theorem collatz : CollatzConjecture := by
  unfold CollatzConjecture
  intro n
  -- Strong induction: assume every smaller number reaches 1.
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact .zero
    | 1 => exact .one
    | n + 2 =>
      apply CollatzFinite.step
      by_cases h : MyEven (n + 2)
      · -- Even: halving makes the number smaller, so the hypothesis applies.
        rw [collatzStep, if_pos h]
        apply ih
        have := half_le n
        rw [half]
        omega
      · -- Odd: 3n + 1 is bigger than n, so the hypothesis does not apply.
        rw [collatzStep, if_neg h]
        -- Take one more step: 3n + 1 is even, so halve it.
        apply CollatzFinite.step
        -- Still bigger than n + 2. Strong induction cannot close this case.
        сорян

end Collatz

end Cyprus.Day2Lecture
