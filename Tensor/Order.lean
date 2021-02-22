class PreOrder (α : Type _) extends HasLessEq α, HasLess α where
    le_refl : (a : α) → a ≤ a
    le_trans : {a b c : α} → a ≤ b → b ≤ c → a ≤ c
    Less := λ a b => a ≤ b ∧ ¬ b ≤ a
    lt_iff_le_not_le : (a b : α) → a < b ↔ (a ≤ b ∧ ¬ b ≤ a)

export PreOrder (le_refl le_trans lt_iff_le_not_le)

section preorder_stuff
variable {α : Type _} [PreOrder α]

theorem le_of_lt {x y : α} (h : x < y) : x ≤ y :=
    ((lt_iff_le_not_le _ _).mp h).1

theorem not_le_of_gt {x y : α} (h : x > y) : ¬ x ≤ y :=
    ((lt_iff_le_not_le _ _).mp h).2

theorem lt_of_le_not_le {x y : α} (h : x ≤ y) (h' : ¬y ≤ x) : x < y :=
    (lt_iff_le_not_le _ _).mpr (And.intro h h')

end preorder_stuff

@[defaultInstance]
instance PreOrder.decidable_lt {α : Type _} [PreOrder α] [DecidableRel (. ≤ . : α → α → Prop)] :
    DecidableRel (. < . : α → α → Prop)
| a, b => if h : a ≤ b then
        if h' : b ≤ a then
            isFalse (λ h'' => not_le_of_gt h'' h')
        else
            isTrue (lt_of_le_not_le h h')
    else
        (isFalse λ h' => h (le_of_lt h') )

class PartialOrder (α : Type _) extends PreOrder α where
    le_antisymm : (a b : α) → a ≤ b → b ≤ a → a = b

class LinearOrder (α : Type _) extends PartialOrder α where
    le_total : (a b : α) → a ≤ b ∨ b ≤ a
    [decidable_le : DecidableRel (HasLessEq.LessEq : α → α → Prop)]
    [decidable_eq : DecidableEq α]
    [decidable_lt : DecidableRel (HasLess.Less : α → α → Prop)]
