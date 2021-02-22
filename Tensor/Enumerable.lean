-- Kyle Miller
import Init.Data.Nat.Basic
import Init.Core
import Tensor.Has

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

/-- A function-backed vector -/
structure Vec (ι : Type u) (α : Type v) where
    toFun : ι → α

macro "vec" xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `Vec.mk xs b

/-- support `v[i]` notation. -/
@[inline] def Vec.getOp (self : Vec ι α) (idx : ι) : α := self.toFun idx

/-- A vector as a function mapping indices to values. -/
class HasVec (β : Type u) (ι : outParam $ Type v) (α : outParam $ Type w) where
    toVec : β → Vec ι α
export HasVec (toVec)

instance : HasVec (Vec ι α) ι α := ⟨ id ⟩

instance [Add α] : Add (Vec ι α) where
    add v w := vec i => v[i] + w[i]
instance [Sub α] : Sub (Vec ι α) where
    sub v w := vec i => v[i] - w[i]
instance [Mul α] : Mul (Vec ι α) where
    mul v w := vec i => v[i] * w[i]
instance [Div α] : Div (Vec ι α) where
    div v w := vec i => v[i] / w[i]

namespace Vec

def push (v : Vec ι (Vec κ α)) : Vec (ι × κ) α := vec p => v[p.1][p.2]
def pop (v : Vec (ι × κ) α) : Vec ι (Vec κ α) := vec i j => v[(i, j)]
def reindex (v : Vec ι α) (f : κ → ι) : Vec κ α := vec i => v[f i]

instance [OfNat α n] : OfNat (Vec ι α) n where
    ofNat := vec i => OfNat.ofNat n

def transpose (v : Vec ι (Vec κ α)) : Vec κ (Vec ι α) := vec j i => v[i][j]

end Vec

def Vec.sum [Enumerable ι] [Add α] [OfNat α Nat.zero] (v : Vec ι α) : α := do
    let mut s : α := 0
    for i in Enumerable.listOf ι do
        s := s + v[i]
    return s

structure DenseVec (ι : Type u) [Enumerable ι] (α : Type v) where
    array : Array α
    hasSize : array.size = Enumerable.card ι

namespace DenseVec
variable {ι : Type u} [Enumerable ι] {α : Type v}

instance [Repr α] : Repr (DenseVec ι α) where
    reprPrec d _ := repr d.array

theorem sizeMapEq (a : Array α) (f : α → β) : (a.map f).size = a.size := sorry

instance [HMul α α₁ α₁] : HMul α (DenseVec ι α₁) (DenseVec ι α₁) where
    hMul r u := ⟨ u.array.map (λ x => r * x) , (sizeMapEq _ _).symm ▸ u.hasSize⟩

def fill (a : α) : DenseVec ι α where
    array := Array.mkArray (Enumerable.card ι) a
    hasSize := Array.size_mkArray ..

def empty [Inhabited α] : DenseVec ι α :=
    fill Inhabited.default

def translateIdx (v : DenseVec ι α) (i : ι) : Fin v.array.size :=
    let ⟨n, h⟩ := Enumerable.enum i
    ⟨n, by rw v.hasSize; exact h⟩

/-- Get the value associated to a particular index. -/
def get (v : DenseVec ι α) (i : ι) : α :=
    v.array.get (v.translateIdx i)

/-- support `v[i]` notation. -/
@[inline] def getOp (self : DenseVec ι α) (idx : ι) : α := self.get idx

instance : HasVec (DenseVec ι α) ι α where
    toVec v := vec i => v[i]

def of [HasVec β ι α] (v : β) : DenseVec ι α where
    array := do
        let v' := toVec v
        let mut a := Array.empty
        for i in Enumerable.listOf ι do
            a := a.push $ v'[i]
        return a
    hasSize := sorry -- need to define differently to be able to easily prove this

/-- Set the value associated to a particular index. -/
def set (v : DenseVec ι α) (i : ι) (a : α) : DenseVec ι α where
    array := v.array.set (v.translateIdx i) a
    hasSize := by rw [Array.size_set, v.hasSize]

def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : DenseVec ι α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
    as.array.forIn b f


instance [HasZero α] [Enumerable ι] : HasZero (DenseVec ι α) where
    zero := ⟨ Array.mkArray (Enumerable.card ι) HasZero.zero, Array.size_mkArray .. ⟩
instance [HasZero α] [Enumerable ι] : OfNat (DenseVec ι α) 0 where
    ofNat := HasZero.zero

def pure (x : α) : DenseVec ι α := fill x

def dot_ (v w : DenseVec ι Float) : Float := do
    let mut s : Float := 0
    for i in Enumerable.listOf ι do
        s := s + v[i] * w[i]
    return s
def add_ [Add α] (v w : DenseVec ι α) : DenseVec ι α := do
    let mut v := v
    for i in Enumerable.listOf ι do
        v := v.set i (v.get i + w.get i)
    return v

-- dsk: alternate add
def add [Add α] [Inhabited α] ( u v : DenseVec ι α) : DenseVec ι α := do
    let mut values := u.array
    for i in [0:values.size] do
        values := values.set! i (values[i] + v.array[i])
    return ⟨ values , sorry ⟩

instance [Add α] [Inhabited α]: Add (DenseVec ι α) where
    add := add

end DenseVec

theorem List.toArraySizeEq (x : List α) : x.toArray.size = x.length := sorry

def List.toDenseVec (x : List α) : DenseVec (Fin x.length) α where
    array := x.toArray
    hasSize := List.toArraySizeEq ..

syntax "![" sepBy(term, ", ") "]" : term

macro_rules
  | `(![ $elems,* ]) => `(List.toDenseVec [ $elems,* ])

example : DenseVec (Fin 3) Nat := ![2,22,222]