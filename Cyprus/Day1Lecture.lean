/-
# Day 1 lecture: logic
-/

import Cyprus.Islanders
import Mathlib.Tactic

namespace Cyprus.Day1Lecture

section Connectives

variable {A B C : Prop}

-- ## Truth and implication

#print True

theorem true_is_true : True := by
  constructor
  -- .intro

#print true_is_true

theorem self_imp : A → A := by
  intro x
  assumption -- exact x
  -- fun x => x

theorem imp_const : A → (B → A) := by
  intros
  assumption
  -- fun x y => x

theorem modus_ponens : A → (A → B) → B := by
  intros
  apply_assumption
  assumption
  -- fun x f => f x

theorem imp_trans : (A → B) → ((B → C) → (A → C)) := by
  intros
  repeat apply_assumption
  -- fun f => fun g => fun x => g (f x)

-- ## Conjunction

-- equiv: A → B → A ∧ B
theorem and_intro (a : A) (b : B) : A ∧ B := by
  constructor <;> trivial

theorem and_left : A ∧ B → A := by
  intro ⟨a, _⟩
  assumption
-- option 5:  And.left
-- option 4:  (·.left)
-- option 3:  fun p => p.left
-- option 2:  fun ⟨a, _⟩ => a
-- option 1:
--  fun p => match p with
--    | ⟨a, _⟩ => a

theorem and_swap : A ∧ B → B ∧ A := by
  intro ⟨x, y⟩
  constructor <;> assumption

-- ## Disjunction

theorem or_intro_left : A → A ∨ B := by
  intro x
  left
  assumption

theorem or_intro_right : B → A ∨ B := by
  intro x
  right
  assumption

theorem or_elim (f : A → C) (g : B → C) : A ∨ B → C := by
  rintro (x | y) <;> solve_by_elim
--  | .inl x => f x
--  | .inr y => g y

theorem or_swap : A ∨ B → B ∨ A := by
  rintro (x | y)
  case inl =>
    right
    assumption
  case inr =>
    left
    assumption

-- ## False and negation

#print False

theorem from_false_anything : False → A := by
  intro
  contradiction
  -- exfalso; assumption
  -- nofun

theorem not_intro (h : A → False) : ¬A := by
  intro
  contradiction

-- no contradiction: look inside, contradiction
theorem no_contradiction : ¬(A ∧ ¬A) := by
  rintro ⟨ha, hna⟩
  contradiction

theorem contrapositive (f : A → B) : ¬B → ¬A := by
  intro nb a
  repeat apply_assumption

-- ## Equivalence

theorem iff_of_imps (f : A → B) (g : B → A) : A ↔ B := by sorry

theorem iff_swap : (A ↔ B) → (B ↔ A) := by sorry

end Connectives

section Tactics

variable {A B C : Prop}

theorem imp_trans_tactic : (A → B) → (B → C) → A → C := by sorry

theorem and_swap_tactic : A ∧ B → B ∧ A := by sorry

theorem or_swap_tactic : A ∨ B → B ∨ A := by sorry

theorem contrapositive_tactic (f : A → B) : ¬B → ¬A := by sorry

theorem not_or_iff : ¬(A ∨ B) ↔ ¬A ∧ ¬B := by sorry

end Tactics

section Classical

variable {A B : Prop}

theorem not_not_elim : ¬¬A → A := by
  -- ¬¬A = (A → False) → False
  intro nna
  cases Classical.em A
  · assumption
  · contradiction

theorem not_and_iff : ¬(A ∧ B) ↔ ¬A ∨ ¬B := by
  constructor
  · intro not_a_and_b
    cases Classical.em A
    · right
      intro b
      apply_assumption
      constructor <;> assumption
    · left; assumption
  · rintro (na | nb) ⟨a, b⟩ <;> contradiction

theorem imp_iff_not_or : (A → B) ↔ ¬A ∨ B := by sorry

end Classical

section Quantifiers

variable {α : Type} {P Q : α → Prop}

theorem forall_imp_of_forall
    (h : ∀ x, P x → Q x) (hp : ∀ x, P x)
    : ∀ x, Q x := by
  intro _
  apply h
  apply hp
-- fun _ => h _ (hp _)

theorem exists_of_forall
    (a : α) (h : ∀ x, P x)
    : ∃ (x : α), P x := by
  exists a
  apply h

theorem exists_or_iff :
    (∃ x, P x ∨ Q x) ↔ (∃ x, P x) ∨ (∃ x, Q x) := by
  constructor
  · rintro ⟨a, (hp | hq)⟩
    · left
      exact ⟨a, hp⟩
    · right
      exists a
  · rintro (⟨a, hp⟩ | ⟨a, hq⟩)
    · exists a
      left
      assumption
    · exists a
      right
      assumption

theorem not_forall_of_exists_not (h : ∃ x, ¬P x) : ¬∀ x, P x := by
  intro hp
  obtain ⟨a, hnp⟩ := h
  apply hnp
  apply hp

end Quantifiers

section KnightsAndKnaves

open Cyprus.Islanders

theorem knight_ne_knave : Role.knight ≠ Role.knave := by sorry

theorem role_dichotomy (r : Role) : r = .knight ∨ r = .knave := by
  cases r
  · left; rfl
  · right; rfl

/-- A says “I am a knave.” -/
def answerSelfAccusation : Answer ["A"] := impossible

theorem puzzleSelfAccusation (A : Islander) (hA : Says A (role A = .knave)) :
    claim% answerSelfAccusation [A] := by
  unfold Says at *
  cases (role_dichotomy (role A)) with
  | inl h =>
    rewrite [h] at hA
    obtain ⟨hAf, hAb⟩ := hA
    suffices Role.knight = Role.knave by contradiction
    apply_assumption
    rfl
  | inr h =>
    rewrite [h] at hA
    obtain ⟨hAf, hAb⟩ := hA
    suffices Role.knave = Role.knight by contradiction
    apply_assumption
    rfl


/-- A says “B is a knight.”  B says “A and I are not the same.” -/
def answerDifferent : Answer ["A", "B"] := sorry

theorem puzzleDifferent (A B : Islander)
    (hA : Says A (role B = .knight)) (hB : Says B (role A ≠ role B)) :
    claim% answerDifferent [A, B] := by
  sorry

/-- A says “We are both knaves.” -/
def answerBothKnaves : Answer ["A", "B"] := sorry

theorem puzzleBothKnaves (A B : Islander)
    (hA : Says A (role A = .knave ∧ role B = .knave)) :
    claim% answerBothKnaves [A, B] := by
  sorry

/-- A says “Everyone on this island is a knave.” -/
def answerAllKnaves : Answer ["A"] := sorry

theorem puzzleAllKnaves (A : Islander) (hA : Says A (∀ x, role x = .knave)) :
    claim% answerAllKnaves [A] := by
  sorry

end KnightsAndKnaves

end Cyprus.Day1Lecture
