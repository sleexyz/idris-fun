module ImplicitRecordFields

-- | Why does Foo typecheck, and not Bar?

record Foo where
  constructor MkFoo
  trivial : (a : Nat) -> (b : Nat) -> a + b = a + b

record Bar where
  constructor MkBar
  trivial : {a : Nat} -> {b : Nat} -> a + b = a + b
