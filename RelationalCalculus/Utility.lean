import Mathlib.Tactic
universe u v

namespace Utility

@[reducible]
def typeof {α : Sort u} (_:α) := α
