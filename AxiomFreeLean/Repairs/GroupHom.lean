import Mathlib.Algebra.Group.Hom.Defs

namespace AxiomFreeLean.Repairs

universe u₁ u₂ u₃

variable {G : Type u₁} {H : Type u₂} {F : Type u₃}

/--
An identical-statement replacement for `map_div'` whose proof follows the
operations exposed by `DivInvMonoid` directly.
-/
theorem zero_map_div' [DivInvMonoid G] [DivInvMonoid H] [FunLike F G H]
    [MulHomClass F G H] (f : F) (hf : ∀ a, f a⁻¹ = (f a)⁻¹) (a b : G) :
    f (a / b) = f a / f b := by
  calc
    f (a / b) = f (a * b⁻¹) := congrArg f (div_eq_mul_inv a b)
    _ = f a * f b⁻¹ := map_mul f a b⁻¹
    _ = f a * (f b)⁻¹ := congrArg (fun x => f a * x) (hf b)
    _ = f a / f b := (div_eq_mul_inv (f a) (f b)).symm

/--
An identical-statement replacement for `map_sub'`. This is the additive
counterpart of `zero_map_div'` and the first repair selected by the
counterfactual-gain data.
-/
theorem zero_map_sub' [SubNegMonoid G] [SubNegMonoid H] [FunLike F G H]
    [AddHomClass F G H] (f : F) (hf : ∀ a, f (-a) = -(f a)) (a b : G) :
    f (a - b) = f a - f b := by
  calc
    f (a - b) = f (a + -b) := congrArg f (sub_eq_add_neg a b)
    _ = f a + f (-b) := map_add f a (-b)
    _ = f a + -(f b) := congrArg (fun x => f a + x) (hf b)
    _ = f a - f b := (sub_eq_add_neg (f a) (f b)).symm

/-- Any proof with the type of `Eq.propIntro` yields propositional extensionality. -/
theorem propext_of_propIntro
    (propIntro : ∀ {a b : Prop}, (a → b) → (b → a) → a = b)
    {a b : Prop} (h : a ↔ b) : a = b :=
  propIntro h.mp h.mpr

/-- A uniform decision procedure for propositions yields excluded middle. -/
theorem em_of_decidesAll
    (decidesAll : ∀ p : Prop, Decidable p) (p : Prop) : p ∨ ¬p :=
  match decidesAll p with
  | .isTrue h => Or.inl h
  | .isFalse h => Or.inr h

end AxiomFreeLean.Repairs
