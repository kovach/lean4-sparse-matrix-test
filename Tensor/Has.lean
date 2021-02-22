-- todo: should have used OfNat?
class HasZero (α : Type _) where zero : α
class HasOne (α : Type _) where one : α
instance : HasZero Nat where zero := 0
instance : HasOne  Nat where one := 1
instance : HasZero Float where zero := 0.0
instance : HasOne  Float where one := 1.0