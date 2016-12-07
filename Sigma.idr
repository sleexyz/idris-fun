module MySigma

%auto_implicits off
record MySigma (a : Type) (P : a -> Type) where
  constructor Pair
  first : a
  second : P first
%auto_implicits on

data IsEven : (n : Nat) -> Type where
  Zero : IsEven 0
  Step : IsEven n -> IsEven (S(S(n)))

foo : MySigma Nat IsEven
foo = Pair 0 Zero

bar : MySigma Nat IsEven
bar = Pair 2 (Step Zero)
