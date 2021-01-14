import Init.Data.Array.Subarray
import Init.Data.Float

macro "exfalso" : tactic => `(apply False.elim)
macro "hm" : tactic => `(apply id)

def fst : α × β → α
| (a, _) => a
def snd : α × β → β
| (_, b) => b

/-- A function-backed vector -/
structure Vec (ι : Type u) (α : Type v) where
    toFun : ι → α

macro "vec" xs:Lean.explicitBinders " => " b:term : term => Lean.expandExplicitBinders `Vec.mk xs b

/-- support `v[i]` notation. -/
@[inline] def Vec.getOp (self : Vec ι α) (idx : ι) : α := self.toFun idx

class HasZero (α : Type _) where zero : α
class HasOne (α : Type _) where one : α
instance : HasZero Nat where zero := 0
instance : HasOne  Nat where one := 1
instance : HasZero Float where zero := 0.0
instance : HasOne  Float where one := 1.0

/-- A vector as a function mapping indices to values. -/
class HasVec (β : Type u) (ι : outParam $ Type v) (α : outParam $ Type w) where
    toVec : β → Vec ι α
export HasVec (toVec)

instance : HasVec (Vec ι α) ι α where
    toVec v := v

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

instance : Monad (Vec ι) where
    pure x := vec i => x
    map f v := vec i => f v[i]
    seq f v := vec i => f[i] v[i]
    bind v f := vec i => (f v[i])[i] -- diagonal (is this actually a monad law?)

instance [OfNat α n] : OfNat (Vec ι α) n where
    ofNat := vec i => OfNat.ofNat n

def transpose (v : Vec ι (Vec κ α)) : Vec κ (Vec ι α) := vec j i => v[i][j]

end Vec

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

class MulComm (α : Type u) [Mul α] where
    mulComm : (x y : α) → x * y = y * x

def Adder (α : Type u) := α


theorem cartEncodeProp {i j m n : Nat} (hi : i < m) (hj : j < n) : i * n + j < m * n := by
    cases m with
    | zero => exfalso; exact Nat.notLtZero _ hi
    | succ m => {
        rw Nat.succMul;
        exact Nat.ltOfLeOfLt (Nat.addLeAddRight (Nat.mulLeMulRight _ (Nat.leOfLtSucc hi)) _) (Nat.addLtAddLeft hj _)
    }

def cartDecode {n m : Nat} (k : Fin (n * m)) : Fin n × Fin m :=
    let ⟨k, h⟩ := k
    (
        ⟨k / m, sorry⟩,
        ⟨k % m, Nat.modLt _ (by { cases m; exfalso; rw Nat.mulZero at h; exact Nat.notLtZero _ h; apply Nat.succPos})⟩
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

def Vec.sum [Enumerable ι] [Add α] [OfNat α Nat.zero] (v : Vec ι α) : α := do
    let mut s : α := 0
    for i in Enumerable.listOf ι do
        s := s + v[i]
    return s

structure DenseVec (ι : Type u) [Enumerable ι] (α : Type v) where
    array : Array α
    hasSize : array.size = Enumerable.card ι

namespace DenseVec
variables {ι : Type u} [Enumerable ι] {α : Type v}

instance [Repr α] : Repr (DenseVec ι α) where
    reprPrec d _ := repr d.array

theorem sizeMapEq (a : Array α) (f : α → β) : (a.map f).size = a.size := sorry

instance [HMul α α₁ α₁] : HMul α (DenseVec ι α₁) (DenseVec ι α₁) where
    hMul r u := ⟨ u.array.map (λ x => r * x) , (sizeMapEq _ _).symm ▸ u.hasSize⟩

def fill (a : α) : DenseVec ι α where
    array := Array.mkArray (Enumerable.card ι) a
    hasSize := Array.sizeMkArrayEq ..

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
    hasSize := by rw [Array.sizeSetEq, v.hasSize]

def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (as : DenseVec ι α) (b : β) (f : α → β → m (ForInStep β)) : m β :=
    as.array.forIn b f


instance [HasZero α] [Enumerable ι] : HasZero (DenseVec ι α) where
    zero := ⟨ Array.mkArray (Enumerable.card ι) HasZero.zero, Array.sizeMkArrayEq .. ⟩
instance [HasZero α] [Enumerable ι] : OfNat (DenseVec ι α) 0 where
    ofNat := HasZero.zero

def pure (x : α) : DenseVec ι α := fill x

-- Kyle's add/dot
-- def dot (v w : DenseVec ι Float) : Float := do
--     let mut s : Float := 0
--     for i in Enumerable.listOf ι do
--         s := s + v[i] * w[i]
--     return s
-- def add [Add α] (v w : DenseVec ι α) : DenseVec ι α := do
--     let mut v := v
--     for i in Enumerable.listOf ι do
--         v := v.set i (v.get i + w.get i)
--     return v

def add [Add α] [Inhabited α] ( u v : DenseVec ι α) : DenseVec ι α := do
    let mut u := u.array
    for i in [0:u.size] do
        u := u.set! i (u[i] + v.array[i])
    return ⟨ u , sorry⟩

instance [Add α] [Inhabited α]: Add (DenseVec ι α) where
    add := add

end DenseVec

theorem List.toArraySizeEq (x : List α) : x.toArray.size = x.length := sorry
-- theorem List.toArraySizeEq (x : List α) : x.toArray.size = x.length := by
--     hm; induction x; exact rfl; rw List.lengthConsEq;
    -- rw Array.sizePushEq

def List.toDenseVec (x : List α) : DenseVec (Fin x.length) α where
    array := x.toArray
    hasSize := List.toArraySizeEq ..

syntax "![" sepBy(term, ", ") "]" : term

macro_rules
  | `(![ $elems,* ]) => `(List.toDenseVec [ $elems,* ])

example : DenseVec (Fin 3) Nat := ![2,22,222]

open Enumerable

class PreOrder (α : Type _) extends HasLessEq α, HasLess α where
    le_refl : (a : α) → a ≤ a
    le_trans : {a b c : α} → a ≤ b → b ≤ c → a ≤ c
    Less := λ a b => a ≤ b ∧ ¬ b ≤ a
    lt_iff_le_not_le : (a b : α) → a < b ↔ (a ≤ b ∧ ¬ b ≤ a)

export PreOrder (le_refl le_trans lt_iff_le_not_le)

section preorder_stuff
variables {α : Type _} [PreOrder α]

theorem le_of_lt {x y : α} (h : x < y) : x ≤ y :=
    ((lt_iff_le_not_le _ _).mp h).1

theorem not_le_of_gt {x y : α} (h : x > y) : ¬ x ≤ y :=
    ((lt_iff_le_not_le _ _).mp h).2

theorem lt_of_le_not_le {x y : α} (h : x ≤ y) (h' : ¬y ≤ x) : x < y :=
    (lt_iff_le_not_le _ _).mpr (And.intro h h')

#check @Eq.mp
#print lt_of_le_not_le
#check propext
end preorder_stuff

#check (. + . : Nat → Nat → Nat)
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

#check (inferInstance : DecidableRel (. < . : Nat → Nat → Prop))

instance : PreOrder Nat where
    le_refl := Nat.leRefl
    le_trans := Nat.leTrans
    lt_iff_le_not_le := λ a b => by {
        apply Iff.intro;
        {
            intro h;
            exact ⟨Nat.leOfLt h, Nat.notLeOfGt h⟩
        };
        { intro | And.intro h h' => {
                exact sorry
            }
        }
    }

class PartialOrder (α : Type _) extends PreOrder α where
    le_antisymm : (a b : α) → a ≤ b → b ≤ a → a = b

class LinearOrder (α : Type _) extends PartialOrder α where
    le_total : (a b : α) → a ≤ b ∨ b ≤ a
    [decidable_le : DecidableRel (HasLessEq.LessEq : α → α → Prop)]
    [decidable_eq : DecidableEq α]
    [decidable_lt : DecidableRel (HasLess.Less : α → α → Prop)]

open PreOrder

def Unfold (σ α : Type _) := σ → Option (α × σ)
structure Ana (σ α : Type _) where
    state : σ
    step : Unfold σ α

namespace Ana

-- TODO might as well have two type parameters
inductive EitherOr (α β : Type _)
| left : α → EitherOr α β
| right : β → EitherOr α β
| both : α → β → EitherOr α β

namespace EitherOr
instance [Repr α] [Repr β] : Repr (EitherOr α β) where
    reprPrec x _ := match x with
    | EitherOr.left a   => "left " ++ repr a
    | EitherOr.right a  => "right " ++ repr a
    | EitherOr.both a b => "both " ++ repr a ++ " " ++ repr b

def reduce (unit : α) (op : α → α → α) : EitherOr α α → α
| EitherOr.left x => op x unit
| EitherOr.right y => op unit  y
| EitherOr.both x y => op x y
end EitherOr

open EitherOr

#check (α : Type _) → (a : α) → Bool

--[s: LinearOrder β] [DecidableRel s.LessEq]
-- def merge_aux [DecidableEq β] [HasLessEq β] [DecidableRel (. ≤ . : β → β → Prop)] : Nat → List (β × α) → List (β × α) → List (β × EitherOr α)
-- | 0, _, _ => []
-- | (n+1), [], ys => ys.map λ ⟨i, a⟩ => ⟨i, right a⟩
-- | (n+1), xs, [] => xs.map λ ⟨i, a⟩ => ⟨i, left a⟩
-- | (n+1), l1@(⟨i, x⟩ :: xs), l2@(⟨j, y⟩ :: ys) =>
--     if i = j then
--         ⟨i, both x y⟩ :: merge_aux n xs ys
--     else if i ≤ j then
--         ⟨i, left x⟩ :: merge_aux n xs l2
--     else
--         ⟨j, right y⟩ :: merge_aux n l1 ys

-- reversed order!
def merge_aux_aux [DecidableEq β] [HasLessEq β] [DecidableRel (. ≤ . : β → β → Prop)] : Nat → List (β × α) → List (β × α) →
    List (β × EitherOr α α) → List (β × EitherOr α α)
| 0, _, _, acc => acc
| (n+1), [], ys, acc => ys.foldl (λ acc (i, a) => (i, right a) :: acc) acc
| (n+1), xs, [], acc => xs.foldl (λ acc (i, a) => (i, left a) :: acc) acc
| (n+1), l1@(⟨i, x⟩ :: xs), l2@(⟨j, y⟩ :: ys), acc =>
    if i = j then
        merge_aux_aux n xs ys (⟨i, both x y⟩ :: acc)
    else if i ≤ j then
        merge_aux_aux n xs l2 (⟨i, left x⟩ :: acc)
    else
        merge_aux_aux n l1 ys ((j, right y) :: acc)

-- def mergeOrList [DecidableEq β] [HasLessEq β] [DecidableRel (. ≤ . : β → β → Prop)] : Nat → List (β × α) → List (β × α) → List (β × EitherOr α α)
-- |  n, xs, ys => merge_aux_aux n xs ys [] |> List.reverse

def mergeIntoArray [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq] :
    Nat → List (β × α) → List (β × α₁) → Array (β × EitherOr α α₁) → Array (β × EitherOr α α₁)
| 0, _, _, acc => acc
| (n+1), [], ys, acc => ys.foldl (λ acc (i, a) => acc.push (i, right a)) acc
| (n+1), xs, [], acc => xs.foldl (λ acc (i, a) => acc.push (i, left a)) acc
| (n+1), l1@(⟨i, x⟩ :: xs), l2@(⟨j, y⟩ :: ys), acc =>
    if i = j then
        mergeIntoArray n xs ys (acc.push ⟨i, both x y⟩)
    else if i ≤ j then
        mergeIntoArray n xs l2 (acc.push ⟨i, left x⟩)
    else
        mergeIntoArray n l1 ys (acc.push (j, right y))

-- def merge'' [DecidableEq β] [HasLessEq β] [DecidableRel (. ≤ . : β → β → Prop)] (xs : List (β × α)) (ys : List (β × α)) : List (β × EitherOr α) :=
-- merge_aux_aux (xs.length + ys.length) xs ys []

--#eval Functor.map (\la
-- def mergeSum [Add α] [DecidableEq β] [HasLessEq β] [DecidableRel (. ≤ . : β → β → Prop)] (xs : List (β × α)) (ys : List (β × α)) : List (β × α) :=
-- (merge' xs ys).map λ (b, m) => (b, reduce m)
-- def mergeSum' [Add α] [DecidableEq β] [HasLessEq β] [DecidableRel (. ≤ . : β → β → Prop)] (xs : Array (β × α)) (ys : Array (β × α)) : Array (β × α) := do
--     let mut res := Array.empty
--     for p in merge_aux (xs.size + ys.size) xs.toList ys.toList do
--         res := res.push ⟨p.1, reduce p.2⟩
--     return res

def scaleArray [HMul α α₁ α₁] (r: α) (u : Array α₁) : Array α₁ :=
    u.map (λ x => r * x)

instance [Mul α] : HMul α (Array α) (Array α) := ⟨ scaleArray ⟩

def mergeIters [o : PreOrder β] [DecidableRel o.LessEq]
    (f g : Unfold σ β) : Unfold (σ×σ) β
    | (s1, s2) => match f s1, g s2 with
        | none, none => none
        | none, some (b,s) => some (b, (s1, s))
        | some (b,s), none => some (b, (s1, s))
        | some (b1,s1'), some (b2,s2') =>
            match decide (b1 ≤ b2) with
            | true => some (b1, (s1', s2))
            | false => some (b2, (s1, s2'))

def listIter : Unfold (List α) α := fun
| [] => none
| x :: tail => some (x, tail)

partial def toList (x : Ana σ α) : List α :=
    match x.step x.state with
    | none => []
    | some (b, s) => b :: toList ⟨ s, x.step ⟩

-- def forIn {α : Type u} {β : Type v} {m : Type v → Type w} [Monad m] (b : β) (x : Ana σ α) (v : σ)
-- (f : α → β → m (ForInStep β)) : m β :=

-- TODO should try rewriting some of these entries with streams:
example [Stream ρ α] [Stream γ α] : Stream (ρ × γ) (EitherOr α α) where
  next? | (s₁, s₂) =>
    match Stream.next? s₁ with
    | none => match Stream.next? s₂ with
        | none => none
        | some (b, s₂) => some (EitherOr.right b, (s₁, s₂))
    | some (a, s₁) => match Stream.next? s₂ with
      | none => some (EitherOr.left a, (s₁, s₂))
      -- todo: compare the values and do the proper merge
      | some (b, s₂) => sorry

end Ana
open Ana

structure Tensor? (ι α : Type _) :=
    locate : ι → α
    σ : Type _
    s₀ : σ
    iter : Stream σ (ι × α)
    sound (s s' : σ) (i : ι) (v : α) : Stream.next? s = some ((i, v), s') → locate i = v
    -- complete? every non-zero (locate ι) is reachable from s₀

def SparseVec ι α := Array (ι × α)

namespace SparseVec

instance [r : Repr (Array (ι × α))] : Repr (SparseVec ι α) := ⟨ r.reprPrec ⟩
instance [r : ToString (Array (ι × α))] : ToString (SparseVec ι α) := ⟨ r.toString ⟩

def sparseAdd [s : Add α] [u : HasZero α] [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq]
    (xs : SparseVec β α ) (ys : SparseVec β α ) : SparseVec β α := do
    let mut res := Array.empty
    for (coord, values) in mergeIntoArray (xs.size + ys.size) xs.toList ys.toList Array.empty do
        res := res.push (coord, EitherOr.reduce u.zero s.add values)
    return res

#eval sparseAdd #[(1,1), (2, 3)] #[(1,1),(2,1)]



#check #[1].map id
def map (f : α → β) (v : SparseVec ι α) : SparseVec ι β :=
Array.map (λ (c, x) => (c, f x)) v

def ofDenseList : List α → SparseVec Nat α
| values => snd $ values.foldr (init := (0, #[])) λ v (n, acc) => (n+1, acc.push (n,v))

instance [HMul α α₁ α₁] : HMul α (SparseVec ι α₁) (SparseVec ι α₁) where
    hMul r v := Array.map (λ (c, x) => (c, r * x)) v

instance [HasZero α] [le: HasLessEq ι] [DecidableEq ι] [DecidableRel le.LessEq] [Add α] : Add (SparseVec ι α) where
    add u v := sparseAdd u v

instance : HasZero (SparseVec ι α) where
    zero := #[]

def mergeAndIntoArray [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq] (n : Nat) (xs : List (β × α₀)) (ys : List (β × α₁))
    : Array (β × (α₀ × α₁)) := do
let rec step
    | 0, _, _, acc => acc
    | (n+1), [], ys, acc => acc
    | (n+1), xs, [], acc => acc
    | (n+1), l1@(⟨i, x⟩ :: xs), l2@(⟨j, y⟩ :: ys), acc =>
        if i = j then
            -- let _ := unsafeIO (IO.print 22)
            step n xs ys (acc.push (i, (x, y)))
        else if i ≤ j then
            step n xs l2 acc
        else
            step n l1 ys acc
step n xs ys #[]

def sparseHMul [s : HMul α α₁ α₁] [Add α₁] [u : HasZero α₁] [DecidableEq ι] [HasLessEq ι]
    [le : HasLessEq ι] [DecidableRel le.LessEq] (xs : SparseVec ι α) (ys : SparseVec ι α₁) : α₁ := do
    let mut res := (u.zero : α₁)
    for (_, (scalar, vector)) in mergeAndIntoArray (xs.size + ys.size) xs.toList ys.toList do
        res := res + scalar * vector
    return res

-- def comb [HasZero α] [Mul α] [Add α] [Inhabited α] [Enumerable ρ] [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
--          (A : List (SparseVec ι α)) (B : SparseVec ι (DenseVec ρ α)) : List (DenseVec ρ α) := do
--     let mut result := []
--     for row in A do
--         let currentRow := sparseHMul row B
--         result := currentRow :: result
--     return result.reverse
def linearCombinationOfRows [HasZero α] [Mul α] [Add α] [Inhabited α] [Enumerable ρ]
    [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
         (A : SparseVec Nat (SparseVec ι α)) (B : SparseVec ι (DenseVec ρ α)) : SparseVec Nat (DenseVec ρ α) := do
    A.map (λ row => sparseHMul row B)
def linearCombinationOfRows' [Mul α] [Add α] [Inhabited α]
    [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
    [HMul α β β] [Add β] [HasZero β]
         (A : SparseVec Nat (SparseVec ι α)) (B : SparseVec ι β) : SparseVec Nat β := do
    A.map (λ row => sparseHMul row B)

-- #eval ((linearCombinationOfRows
-- [#[(1,3), (4,2)],
--  #[(3,2)]]

--  #[(1, ![4,5]),
--    (3, ![1,2])]).map DenseVec.array : List (Array Nat))

-- #eval ((linearCombinationOfRows
-- [#[(1,3), (4,2)],
--  #[(3,2)]]

--  #[(1, ![4,5])]).map DenseVec.array : List (Array Nat))

#check Array.set!
def sparseTranspose (n : Nat) (A : SparseVec Nat (SparseVec Nat α)) : SparseVec Nat (SparseVec Nat α) := do
    let mut out := Array.mkArray n (0, #[])
    for (rowC, row) in A do
        for (coord, value) in row do
            out := Array.set! out (coord-1) (coord, out[coord-1].2.push (rowC, value))
    return out

def printMat (mat : SparseVec Nat (SparseVec Nat Float)) : IO Unit := do
    for (i, row) in mat do
        for (j, value) in row do
            IO.println s!"{i} {j} {value}"

end SparseVec


def kyle_main : IO UInt32 := do
    let mut v : DenseVec (Fin 3) Nat := ![2,22,222]
    v := DenseVec.of $ toVec v + toVec v + 2
    for x in v do
        IO.println s!"elt of v is {x}"
    let s : Nat := Vec.sum $ toVec v
    IO.println s!"sum = {s}"
    return 0

def range (n : Nat) : List Nat := do
    let mut result := []
    for x in [0:n] do
        result := x :: result
    return result.reverse

section ParsingMtx

-- namespace Float
-- @[extern c inline "(- #1)"]   constant neg : Float → Float
-- instance : Neg Float       := neg⟩
-- #check Float.neg
-- #check Float.ofScientific
-- #eval (Float.ofScientific 5 true 0)
-- end Float

def parseFloat! : String → Float
| str => do
    let mut (sign, digits) : (Bool × String) := if str.front == '-' then (true, str.drop 1) else (false, str)
    let pred c := c.isDigit
    let (int, digits) := (Float.ofScientific (digits.takeWhile pred).toNat! false 0, digits.dropWhile pred)
    let fracStr := String.takeWhile (digits.drop 1) pred
    let frac := Float.ofScientific (fracStr.toNat!) true fracStr.length
    if sign then 0.0 - (int + frac) else int + frac

#eval parseFloat! "-3.534"

def build : IO (Nat × SparseVec Nat (SparseVec Nat Float)) := do
    let ValueType := Float
    let bench_too_large := "../../taco/benchmarks/thermomech_dK/thermomech_dK.mtx"
    let benchSmall := "../../taco/benchmarks/sherman2/sherman2.mtx"
    let benchTiny := "../../taco/benchmarks/test.mtx"
    let input ← IO.FS.readFile benchSmall
    let mut result : SparseVec Nat (SparseVec Nat ValueType) := #[]
    let mut currentRowIndex : Nat := 1 -- TODO read from first line
    let mut currentRow : SparseVec Nat ValueType := #[]
    let mut nnz := 0
    let lines := List.dropWhile (λ line => line.front == '%') (input.splitOn "\n")
    for line in lines.drop 1 do {
        nnz := nnz + 1
        let data := line.splitOn " "
        match data with
        | [col, row, value] =>
            let rowN := row.toNat!
            if rowN != currentRowIndex then
                result := result.push (currentRowIndex, currentRow)
                currentRowIndex := rowN
                currentRow := #[]
            currentRow := currentRow.push (col.toNat!, parseFloat! value)
        | _ => nnz := nnz -- issue? return ()  no good
    }
    result := result.push (currentRowIndex, currentRow)
    let n := currentRowIndex
    -- result := result[:10000]
    IO.println s!"rows: {n}"
    IO.println s!"nnz:  {nnz}"
    return (n, SparseVec.sparseTranspose n result)

end ParsingMtx

open DenseVec
open SparseVec

#check (HasZero.zero : DenseVec (Fin 3) Nat)
#check ofDenseList $ range 10 |> List.map λ i => (fill 1 : DenseVec (Fin 1) Nat)

def junkMatrix : Unit := do
    let inputDim := Fin 1
    let zd : DenseVec inputDim Nat := fill 1
    let Bsd : SparseVec Nat (DenseVec inputDim Nat) := ofDenseList (range 1100 |> List.map λ i => fill 1)
    let Bss : SparseVec Nat (SparseVec Nat Nat) := ofDenseList (range 1100 |> List.map λ i => #[(1,1)])
    let B' :=  #[(1, zd), (2, zd)]
    ()

def main : IO UInt32 := do
    let (n, A) ← build
    -- printMat A'
    IO.println ""
    -- printMat A
    let A' := sparseTranspose n A
    IO.println "computing"
    let out := SparseVec.linearCombinationOfRows' A' A
    IO.println "printing result"
    IO.println s!"num nonzero rows: {out.size}"

    for (index, row) in out[0:5] do
        IO.println s!"{index}: {row[0:8].toArray}"

    IO.println "done"
    return 0