/-
x := Sparse ⬝ (Dense * v)
x := Sparse ⬝ ((Dense : Vec) *  v)
-/
import Init.Data.Stream

inductive f (α β : Type _) where
| cons (head : α) (tail : β) : f α β
| stream (state : β) : f α β
deriving Repr

def next? [h : Stream β α] (s : f α β) : Option (α × β) :=
match s with
| f.cons x xs => some (x, xs)
| f.stream s => h.next? s

structure obj (α β : Type _) where
    index : β
    value : α
    deriving Repr

partial def mergeIntersectionStep [Stream σ₁ (obj α₁ β)] [Stream σ₂ (obj α₂ β)]
    [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq]
    (s : f (obj α₁ β) σ₁) (t : f (obj α₂ β) σ₂)
    : Option (Option (obj (α₁×α₂) β) × (f (obj α₁ β) σ₁) × (f (obj α₂ β) σ₂)) :=
    match next? s, next? t with
    | none, _ => none
    | _, none => none
    | some (v1, s1), some (v2, t1) =>
        if v1.index = v2.index
        then some (some {index := v1.index, value := (v1.value, v2.value)}, f.stream s1, f.stream t1)
        else if v1.index ≤ v2.index
        then some (none, f.stream s1, f.cons v2 t1)
        else some (none, f.cons v1 s1, f.stream t1)

partial def mergeIntersection [Stream σ₁ (obj α₁ β)] [Stream σ₂ (obj α₂ β)]
    [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq]
    (s : f (obj α₁ β) σ₁) (t : f (obj α₂ β) σ₂) : Option (obj (α₁×α₂) β × (σ₁×σ₂)) :=
    match next? s, next? t with
    | none, _ => none
    | _, none => none
    | some (v1, s1), some (v2, t1) =>
        if v1.index = v2.index
        then some ({index := v1.index, value := (v1.value, v2.value)}, (s1, t1))
        else if v1.index ≤ v2.index
        then mergeIntersection (f.stream s1) (f.cons v2 t1)
        else mergeIntersection (f.cons v1 s1) (f.stream t1)

instance : Stream (Nat×List α) (obj α Nat) where
next?
    | (n, []) => none
    | (n, x :: xs) => some (⟨n, x⟩, (n+1, xs))

#eval mergeIntersectionStep (f.stream (0, [1,2])) (f.stream (1, [2,3]))

-- instance intersection [Stream σ₁ (β×α₁)] [Stream σ₂ (β×α₂)]
--     [DecidableEq β] [le : HasLessEq β] [DecidableRel le.LessEq]
--     (n : Nat) : Stream (Peek σ₁ α₁ × Peek σ₂ α₂) (β×α₁×α₂) where
-- next? s :=
-- let (⟨(i1,h1),t1⟩, ⟨(i2,h2),t2⟩) :=
-- if i1 = i2 then some ((i1, h1, h2),

def test (z : Nat) : Nat := do
    let mut x := 1
    let mut y := 3
    return x + y + z

#reduce test