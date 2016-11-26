module Main


main : IO ()
main = putStrLn "hello world"

record Person where
  constructor MkPerson
  first, last : String
  age : Int


fred : Person
fred = MkPerson "Fred" "Bloggs" 30

total
plusIdL : (n : Nat) -> 0 + n = n
plusIdL n = Refl

-- * Playing with inductive proofs:

total
plusIdR : (n : Nat) -> n + 0 = n
plusIdR Z = Refl
plusIdR (S n) = rewrite plusIdR n in Refl

total
plusIdR' : (n : Nat) -> n + 0 = n
plusIdR' Z = Refl
plusIdR' (S n) = cong {f=S} (plusIdR' n)
