import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Positivity.Core

/-!

It has been debated whether to make a positivity extension to show `0 < Fintype.card X` when
typeclass inference can find the nonemptiness of the fintype `X`.  For example, see

https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/Could.20positivity.20handle.20sums.20of.20squares.3F/near/398074551

The consensus seems to be in favour, so let's enable it for this project and see what happens.

-/

namespace Mathlib.Meta.Positivity

open Lean Meta Qq Function

/-- Extension for the `positivity` tactic: cardinalities of nonempty fintypes are positive. -/
@[positivity Fintype.card _]
def evalFintypeCard : PositivityExt where eval {_ _} _zα _pα e := do
  let .app (.app _ a) _ ← whnfR e | throwError "not Fintype.card"
  let p ← mkAppOptM ``Fintype.card_pos #[a, none, none]
  pure (.positive p)
