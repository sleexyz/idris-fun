module Structural

%auto_implicits off
%auto_implicits on

-- Before we can get structural types, i.e. row types, we need sets

-- Good ol' lists...

namespace List'

  using (a : Type)
    data List' : a -> Type where
      Nil : List' a
      (::) : a -> List' a -> List' a


-- Lists of dependent pairs:

namespace DepList

  DepList : (a : Type) -> (P : a -> Type) -> Type
  DepList a P = List $ DPair a P

  test1 : DepList Int (\_ => Int)
  test1 = Nil

  test2 : DepList Int (\_ => Int)
  test2 = MkDPair 1 2 :: Nil

  test3 : DepList Int (\_ => Int)
  test3 = [ MkDPair 1 2 ]


-- Generalized indexed vectors, take 1

namespace IVec1
  -- Indexing Scheme

  record Scheme (a : Type) (i : Type) where
    constructor MkScheme
    init : i
    getNext : a -> i -> i


  using (a : Type, i : Type, s : Scheme a i, state : i)
    data IVec : Scheme a i -> i -> Type where
      Nil : IVec s (init s)
      (::) : (x : a) -> IVec s state -> IVec s ((getNext s) x state)

  -- We can recover length-indexed vectors with this representation

  LiVec : Type -> Nat -> Type
  LiVec a n = IVec s n
    where
      s : Scheme a Nat
      s = MkScheme Z (const S)

  test1 : LiVec String 0
  test1 = Nil

  test2 : LiVec String 1
  test2 = ["hello"]

  test3 : LiVec String 2
  test3 = ["hello", "world"]


  -- But can we recover preconditions on our state transition?
  -- The goal is to encode uniqueness of fields during construction
