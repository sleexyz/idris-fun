module GeneralizedIndexedVectors

%default total
-- * In idris, interfaces are limited to types.

data Vector : Type-> Nat -> Type where
  Nil : Vector a 0
  (::) : a -> Vector a n -> Vector a (S n)


get : (n : Nat) -> Vector a m -> (LT n m) -> a
get Z Nil LTEZero impossible
get Z (x :: xs) p = x
get (S a) Nil LTEZero impossible
get (S a) (x :: xs) p = get a xs (succMonotonic p)
  where
    succMonotonic : LTE (S n) (S m) -> LTE n m
    succMonotonic (LTESucc p) = p


interface HasWitness a where
  Witness : a

HasWitness (LTE Z m) where
  Witness = LTEZero

HasWitness (LTE n m) => HasWitness (LTE (S n) (S m)) where
  Witness = LTESucc Witness


-- Hack to get around idris typeclasses restricted on types
%auto_implicits off
data GetProp : Nat -> Nat -> Type where
  WrapGetAuto : {n, m : Nat} -> (getAuto : {a : Type} -> ((HasWitness (LTE (S n) m)) => (n : Nat) -> Vector a m -> a)) -> GetProp n m
%auto_implicits on


HasWitness (GetProp Z m) where
  Witness = WrapGetAuto (\n => \xs => get Z xs Witness)

HasWitness (LTE (S n) m) => HasWitness (GetProp (S n) m) where
  Witness = WrapGetAuto (\(S n) => \(x :: xs) => get n xs Witness)

