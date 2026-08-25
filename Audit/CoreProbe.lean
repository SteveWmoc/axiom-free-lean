import Std

universe u v

theorem zero_proof_irrelevance (P : Prop) (p q : P) : p = q := rfl

theorem zero_nat_add_comm (m n : Nat) : m + n = n + m := Nat.add_comm m n

theorem zero_nat_mul_comm (m n : Nat) : m * n = n * m := Nat.mul_comm m n

theorem zero_list_map_id (xs : List α) : xs.map id = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map, ih]
    rfl

theorem zero_subtype_ext {α : Sort u} {p : α → Prop} (x y : Subtype p)
    (h : x.val = y.val) : x = y := by
  cases x
  cases y
  cases h
  rfl

theorem uses_funext {α : Sort u} {β : α → Sort v} (f g : (x : α) → β x)
    (h : ∀ x, f x = g x) : f = g :=
  funext h

theorem uses_propext (P Q : Prop) (h : P ↔ Q) : P = Q :=
  propext h

theorem uses_quot_sound {α : Sort u} {r : α → α → Prop} (a b : α)
    (h : r a b) : Quot.mk r a = Quot.mk r b :=
  Quot.sound h

theorem uses_set_ext {α : Sort u} (s t : α → Prop)
    (h : ∀ x, s x ↔ t x) : s = t :=
  funext fun x => propext (h x)

theorem uses_excluded_middle (P : Prop) : P ∨ ¬ P :=
  Classical.em P

#print axioms zero_proof_irrelevance
#print axioms zero_nat_add_comm
#print axioms zero_nat_mul_comm
#print axioms zero_list_map_id
#print axioms zero_subtype_ext
#print axioms funext
#print axioms uses_funext
#print axioms propext
#print axioms uses_propext
#print axioms Quot.sound
#print axioms uses_quot_sound
#print axioms uses_set_ext
#print axioms Classical.choice
#print axioms Classical.em
#print axioms uses_excluded_middle
