module Category

-- * Unfortunately, it's not as easy to justify definining a parameterized category typeclass in the Idris Prelude

-- * The reason is because (->) is not a type constructor

interface Cat (k : Type) (mor : k -> k -> Type) where
  id : {a : k} -> mor a a
  comp : {a : k} -> {b : k} -> {c : k} -> mor b c -> mor a b -> mor a c


-- * A work around is to use a wrapper type around morphisms:

infixr 0 ~>

data (~>) : Type -> Type -> Type where
  Wrap : (a -> b) -> a ~> b

Unwrap : a ~> b -> a -> b
Unwrap (Wrap f) = f

implementation [idris_wrapped] Cat Type (~>) where
  id = Wrap id
  comp (Wrap g) (Wrap f) =  Wrap (g . f)

-- * But that's kinda icky
