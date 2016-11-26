-- * Binary / Nat conversion

module NatBin

data Bin : Type where
  BZero : Bin
  BTwice : Bin -> Bin
  BSTwice : Bin -> Bin

total
bincr : Bin -> Bin
bincr BZero = BSTwice BZero
bincr (BTwice x) = BSTwice x
bincr (BSTwice x) = BTwice (bincr x)

total
bin2nat : Bin -> Nat
bin2nat BZero = 0
bin2nat (BTwice x) = 2 * (bin2nat x)
bin2nat (BSTwice x) = 2 * (bin2nat x) + 1

total
nat2bin : Nat -> Bin
nat2bin Z = BZero
nat2bin (S k) = bincr (nat2bin k)

total
bin2natSucc : (b : Bin) -> bin2nat (bincr b) = S (bin2nat b)
bin2natSucc BZero = Refl
bin2natSucc (BTwice x) =
  rewrite plusCommutative (bin2nat x + (bin2nat x + 0)) 1 in
  Refl
bin2natSucc (BSTwice x) =
  rewrite bin2natSucc x in
  rewrite plusZeroRightNeutral (bin2nat x) in
  rewrite sym $ plusSuccRightSucc (bin2nat x) (bin2nat x) in
  rewrite plusCommutative (bin2nat x +  bin2nat x) 1 in
  Refl

total
conversionIdNat : (n : Nat) -> (bin2nat (nat2bin n)) = n
conversionIdNat Z = Refl
conversionIdNat (S n) =
  rewrite bin2natSucc (nat2bin n) in
  rewrite conversionIdNat n in
  Refl

total
bnorm : Bin -> Bin
bnorm = nat2bin . bin2nat

total
bnormIdemp : (b : Bin) -> bnorm (bnorm b) = bnorm b
bnormIdemp b =
  rewrite (conversionIdNat (bin2nat b)) in
  Refl

total
conversionIdNormalizedBin : (b : Bin) -> nat2bin (bin2nat (bnorm b)) = bnorm b
conversionIdNormalizedBin = bnormIdemp
