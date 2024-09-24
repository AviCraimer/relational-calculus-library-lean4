
namespace Logic
notation "⋆" => PUnit.unit -- \*
notation "{⋆}" => PUnit --

@[simp]
theorem forall_punit(P : (a: {⋆}) → Prop)  : (∀ (a: {⋆}), P a) = (P ⋆) := by
simp
constructor
· intro h
  specialize h ⋆ ; exact h
· intro Pstar a
  cases a
  exact Pstar
