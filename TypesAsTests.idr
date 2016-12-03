
module TypesAsTests

data Test = Result (List String -> List String)

runTest : Test -> List String
runTest (Result x) = (x [])

nop : Test
nop = Result id

fail : String -> Test
fail str = Result (\x => (str :: x))

shouldBe : (Eq a, Show a) => a -> a -> Test
shouldBe x y = if (x == y) then nop else fail ("Fail: " ++ show x ++ " is not equal to " ++ show y)

(>>) : Test -> Test -> Test
(Result x) >> (Result y) = (Result (x . y))


tests : Test
tests = shouldBe 1 1 >> shouldBe 2 2

-- checkTests : (runTest tests) = []
-- checkTests = Refl

main : IO ()
main = putStrLn $ show $ (\x => if x then "asdf" else "2929929") (TypesAsTests.Test == TypesAsTests.Test)
