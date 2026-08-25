import Mathlib

namespace AxiomFreeLean

universe u

theorem zero_decidable_em (P : Prop) [decision : Decidable P] : P ∨ ¬ P :=
  match decision with
  | .isTrue h => Or.inl h
  | .isFalse h => Or.inr h

theorem zero_not_not_em (P : Prop) : ¬¬(P ∨ ¬ P) := by
  intro h
  apply h
  exact Or.inr fun hp => h (Or.inl hp)

theorem zero_list_map_id_pointwise (xs : List α) : xs.map id = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change id x :: xs.map id = x :: xs
      exact congrArg (List.cons x) ih

theorem zero_reverseAux_reverseAux_nil {as bs : List α} :
    List.reverseAux (List.reverseAux as bs) [] = List.reverseAux bs as := by
  induction as generalizing bs with
  | nil => rfl
  | cons a as ih => exact ih (bs := a :: bs)

theorem zero_list_reverse_reverse (as : List α) : as.reverse.reverse = as := by
  change List.reverseAux (List.reverseAux as []) [] = as
  exact zero_reverseAux_reverseAux_nil (as := as) (bs := [])

theorem zero_eq_zero_of_zero_dvd {n : Nat} : 0 ∣ n → n = 0
  | ⟨k, h⟩ => h.trans (Nat.zero_mul k)

theorem zero_nat_le_of_dvd {m n : Nat} (positive : 0 < n) : m ∣ n → m ≤ n
  | ⟨0, equality⟩ => by
      cases equality
      exact False.elim (Nat.not_succ_le_zero 0 positive)
  | ⟨k + 1, equality⟩ => by
      cases equality
      have h : m * 1 ≤ m * (k + 1) := Nat.mul_le_mul_left m (Nat.succ_pos k)
      exact Eq.mp (congrArg (fun left => left ≤ m * (k + 1)) (Nat.mul_one m)) h

theorem zero_nat_dvd_antisymm : ∀ {m n : Nat}, m ∣ n → n ∣ m → m = n
  | _, 0, _, h₂ => zero_eq_zero_of_zero_dvd h₂
  | 0, _, h₁, _ => (zero_eq_zero_of_zero_dvd h₁).symm
  | m + 1, n + 1, h₁, h₂ =>
      Nat.le_antisymm
        (zero_nat_le_of_dvd (Nat.succ_pos n) h₁)
        (zero_nat_le_of_dvd (Nat.succ_pos m) h₂)

def PointwiseSetEq {α : Type u} (s t : Set α) : Prop :=
  ∀ x, x ∈ s ↔ x ∈ t

theorem zero_pointwise_union_comm (s t : Set α) :
    PointwiseSetEq (s ∪ t) (t ∪ s) := fun _ =>
  ⟨fun h => h.elim Or.inr Or.inl, fun h => h.elim Or.inr Or.inl⟩

end AxiomFreeLean
