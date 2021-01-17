import Init.Data.Array.Subarray
import Init.Data.Float
import Tensor.Order
import Tensor.Enumerable

section Util
def fst : α × β → α
| (a, _) => a
def snd : α × β → β
| (_, b) => b
def range (n : Nat) : List Nat := do
    let mut result := []
    for x in [0:n] do
        result := x :: result
    return result.reverse
end Util

class HasZero (α : Type _) where zero : α
class HasOne (α : Type _) where one : α
instance : HasZero Nat where zero := 0
instance : HasOne  Nat where one := 1
instance : HasZero Float where zero := 0.0
instance : HasOne  Float where one := 1.0

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


open PreOrder


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

def exAdd1 := ()
def sparseAdd [s : Add α] [u : HasZero α] [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq]
    (xs ys : SparseVec β α ) : SparseVec β α := do
    let mut res := Array.empty
    for (coord, values) in mergeIntoArray (xs.size + ys.size) xs.toList ys.toList Array.empty do
        res := res.push (coord, EitherOr.reduce u.zero s.add values)
    return res

#eval sparseAdd #[(1, 1), (2, 3)] #[(1,1),(2,1)]

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
instance : Inhabited (SparseVec ι α) := ⟨ HasZero.zero ⟩

def mergeAndIntoArray [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq] (n : Nat)
    (xs : List (β × α₀)) (ys : List (β × α₁))
    : Array (β × (α₀ × α₁)) := do
let rec step
    | 0, _, _,       acc => acc
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

def hMulDot [s : HMul α α₁ α₁] [Add α₁] [u : HasZero α₁] [DecidableEq ι] [HasLessEq ι]
    [le : HasLessEq ι] [DecidableRel le.LessEq] (xs : SparseVec ι α) (ys : SparseVec ι α₁) : α₁ := do
    let mut res := (u.zero : α₁)
    for (_, (scalar, vector)) in mergeAndIntoArray (xs.size + ys.size) xs.toList ys.toList do
        res := res + scalar * vector
    return res

def linearCombinationOfRows [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
    [HMul α β β] [Add β] [HasZero β]
         (A : SparseVec Nat (SparseVec ι α)) (B : SparseVec ι β) : SparseVec Nat β := do
    A.map (λ row => hMulDot row B)

instance [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
    [HMul α β β] [Add β] [HasZero β]
    : HMul (SparseVec Nat (SparseVec ι α)) (SparseVec ι β) (SparseVec Nat β) :=
    ⟨ linearCombinationOfRows ⟩

def sparseTranspose (n : Nat) (A : SparseVec Nat (SparseVec Nat α)) : SparseVec Nat (SparseVec Nat α) := do
    let mut out := Array.mkArray n (0, #[])
    for (rowC, row) in A do
        for (coord, value) in row do
            out := Array.set! out (coord-1) (coord, out[coord-1].2.push (rowC, value))
    return out
-- todo: remove Nat arg
-- postfix:max "ᵀ" => sparseTranspose

def printMat (mat : SparseVec Nat (SparseVec Nat Float)) : IO Unit := do
    for (i, row) in mat do
        for (j, value) in row do
            IO.println s!"{i} {j} {value}"

end SparseVec

def Matrix := SparseVec Nat (SparseVec Nat Float)