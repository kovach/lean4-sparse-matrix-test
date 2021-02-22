-- Scott Kovach
import Init.Data.Array.Subarray
import Init.Data.Float
import Std.Data.RBMap

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

-- could have used `partial def`
def mergeUnion [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq] :
    Nat → List (β × α) → List (β × α₁) → Array (β × EitherOr α α₁) → Array (β × EitherOr α α₁)
| 0, _, _, acc => acc
| (n+1), [], ys, acc => ys.foldl (λ acc (i, a) => acc.push (i, right a)) acc
| (n+1), xs, [], acc => xs.foldl (λ acc (i, a) => acc.push (i, left a)) acc
| (n+1), l1@(⟨i, x⟩ :: xs), l2@(⟨j, y⟩ :: ys), acc =>
    if i = j then
        mergeUnion n xs ys (acc.push ⟨i, both x y⟩)
    else if i ≤ j then
        mergeUnion n xs l2 (acc.push ⟨i, left x⟩)
    else
        mergeUnion n l1 ys (acc.push (j, right y))

def scaleArray [HMul α α₁ α₁] (r: α) (u : Array α₁) : Array α₁ :=
    u.map (λ x => r * x)

instance [Mul α] : HMul α (Array α) (Array α) := ⟨ scaleArray ⟩

@[reducible]
def SparseVec ι α := Array (ι × α)

namespace SparseVec

-- needed without `reducible` attribute (also needs ForIn)
-- instance [r : Repr (Array (ι × α))] : Repr (SparseVec ι α) := ⟨ r.reprPrec ⟩
-- instance [r : ToString (Array (ι × α))] : ToString (SparseVec ι α) := ⟨ r.toString ⟩

-- todo: use algebraic class instead of OfNat
def sparseAdd [s : Add α] [OfNat α 0] [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
    (xs ys : SparseVec ι α ) : SparseVec ι α := do
    let mut res := Array.empty
    for (coord, values) in mergeUnion (xs.size + ys.size) xs.toList ys.toList Array.empty do
        res := res.push (coord, EitherOr.reduce 0 s.add values)
    return res

#eval sparseAdd #[(1,3), (5,4)] #[(1,5), (2,1)]

def map (f : α → β) (v : SparseVec ι α) : SparseVec ι β :=
    Array.map (λ (c, x) => (c, f x)) v

def ofDenseList : List α → SparseVec Nat α
| values => Prod.snd $ values.foldr (init := (0, #[])) λ v (n, acc) => (n+1, acc.push (n,v))

instance [HMul α α₁ α₁] : HMul α (SparseVec ι α₁) (SparseVec ι α₁) where
    hMul r v := Array.map (λ (c, x) => (c, r * x)) v

instance [OfNat α 0] [le: HasLessEq ι] [DecidableEq ι] [DecidableRel le.LessEq] [Add α] : Add (SparseVec ι α) where
    add u v := sparseAdd u v

instance : OfNat (SparseVec ι α) 0 where
    ofNat := #[]
instance : Inhabited (SparseVec ι α) := ⟨ #[] ⟩

def mergeIntersection [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq] (n : Nat)
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

def hMulDot [s : HMul α α₁ α₁] [Add α₁] [OfNat α₁ 0] [DecidableEq ι] [HasLessEq ι]
    [le : HasLessEq ι] [DecidableRel le.LessEq] (xs : SparseVec ι α) (ys : SparseVec ι α₁) : α₁ := do
    let mut res := 0
    for (_, (scalar, vector)) in mergeIntersection (xs.size + ys.size) xs.toList ys.toList do
        res := res + scalar * vector
    return res

def linearCombinationOfRows [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
    [s : HMul α β β] [Add β] [OfNat β 0]
         (A : SparseVec Nat (SparseVec ι α)) (B : SparseVec ι β) : SparseVec Nat β := do
    A.map (λ row => hMulDot (s := s) row B)

instance [DecidableEq ι] [le : HasLessEq ι] [DecidableRel le.LessEq]
    [HMul α β β] [Add β] [OfNat β 0]
    : HMul (SparseVec Nat (SparseVec ι α)) (SparseVec ι β) (SparseVec Nat β) :=
    ⟨ linearCombinationOfRows ⟩

def sparseTranspose (A : SparseVec Nat (SparseVec Nat α)) : SparseVec Nat (SparseVec Nat α) := do
  let mut temp := Std.mkRBMap Nat (SparseVec Nat α) (. < .)
  for (rowC, row) in A do
    for (coord, value) in row do
      temp := temp.insert coord (temp.findD coord #[] |>.push (rowC, value))
  return temp.fold (fun ps k v => ps.push (k, v)) #[]

postfix:max "ᵀ" => sparseTranspose

def printMat (mat : SparseVec Nat (SparseVec Nat Float)) : IO Unit := do
    for (i, row) in mat do
        for (j, value) in row do
            IO.println s!"{i} {j} {value}"

end SparseVec

def Matrix := SparseVec Nat (SparseVec Nat Float)