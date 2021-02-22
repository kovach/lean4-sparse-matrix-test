import Init.Data.Nat.Basic
import Init.Core

macro "exfalso" : tactic => `(apply False.elim)

def Function.leftInverse (g : β → α) (f : α → β) : Prop :=
    ∀ x, g (f x) = x
def Function.rightInverse (g : β → α) (f : α → β) : Prop :=
    Function.leftInverse f g

structure Equiv (α : Sort u) (β : Sort v) where
    toFun : α → β
    invFun : β → α
    leftInv : Function.leftInverse invFun toFun
    rightInv : Function.rightInverse invFun toFun

infix:25 " ≃ " => Equiv

def Equiv.symm (f : α ≃ β) : β ≃ α where
    toFun := f.invFun
    invFun := f.toFun
    leftInv := f.rightInv
    rightInv := f.leftInv

/-- An equivalence "is" a function. -/
instance (α : Type u) (β : Type v) : CoeFun (Equiv α β) (λ _ => α → β) where
    coe := Equiv.toFun

class Enumerable (α : Type u) where
    card : Nat
    enum : α ≃ Fin card

#check Nat.succ_mul
theorem cartEncodeProp {i j m n : Nat} (hi : i < m) (hj : j < n) : i * n + j < m * n := by
    cases m with
    | zero => exfalso; exact Nat.notLtZero _ hi
    | succ m => {
        rw [Nat.succ_mul];
        exact Nat.ltOfLeOfLt (Nat.addLeAddRight (Nat.mulLeMulRight _ (Nat.leOfLtSucc hi)) _) (Nat.addLtAddLeft hj _)
    }

def cartDecode {n m : Nat} (k : Fin (n * m)) : Fin n × Fin m :=
    let ⟨k, h⟩ := k
    (
        ⟨k / m, sorry⟩,
        ⟨k % m, Nat.modLt _ (by { cases m; exfalso; rw Nat.mul_zero at h; exact Nat.notLtZero _ h; apply Nat.succPos})⟩
    )

instance [Enumerable α] [Enumerable β] : Enumerable (α × β) where
    card := Enumerable.card α * Enumerable.card β
    enum := {
        toFun := λ (a, b) =>
            let ⟨i, hi⟩ := Enumerable.enum a
            let ⟨j, hj⟩ := Enumerable.enum b
            ⟨i * Enumerable.card β + j, cartEncodeProp hi hj⟩
        invFun := λ n =>
            let (i, j) := cartDecode n
            (Enumerable.enum.symm i, Enumerable.enum.symm j)
        leftInv := sorry
        rightInv := sorry
    }

instance : Enumerable (Fin n) where
    card := n
    enum := {
        toFun := id
        invFun := id
        leftInv := λ _ => rfl
        rightInv := λ _ => rfl
    }

instance : Enumerable Bool where
    card := 2
    enum := {
        toFun := fun
        | false => 0
        | true => 1
        invFun := fun
        | ⟨0, _⟩ => false
        | ⟨1, _⟩ => true
        | ⟨n+2, h⟩ => False.elim (Nat.notSuccLeZero _ (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc h)))
        leftInv := fun
            | true => rfl
            | false => rfl
        rightInv := fun
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
            | ⟨n+2, h⟩ => False.elim (Nat.notSuccLeZero _ (Nat.leOfSuccLeSucc (Nat.leOfSuccLeSucc h)))
    }

instance : Enumerable Empty where
    card := 0
    enum := {
        toFun := fun t => nomatch t
        invFun := fun
        | ⟨n, h⟩ => False.elim (Nat.notSuccLeZero _ h)
        leftInv := fun t => nomatch t
        rightInv := fun t => nomatch t
    }

def Enumerable.listOf.aux (α : Type u) [Enumerable α] : Nat -> Nat -> List α
| lo, 0 => []
| lo, (left+1) =>
    if h : lo < Enumerable.card α then
        Enumerable.enum.symm ⟨lo, h⟩ :: aux α (lo + 1) left
    else [] -- Shouldn't happen, but makes the definition easy.

/-- Create a list of every term in the Enumerable type in order. -/
def Enumerable.listOf (α : Type u) [Enumerable α] : List α :=
    Enumerable.listOf.aux α 0 (Enumerable.card α)
