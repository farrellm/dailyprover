module Common.Lte

import Data.Fin

%access export

%default total

fromEqLte : (l = r) -> LTE l r
fromEqLte prf = rewrite prf in lteRefl

lteAddBoth : LTE n m -> LTE (c + n) (c + m)
lteAddBoth {c = Z} lte = lte
lteAddBoth {c = (S k)} lte =
  let ind = lteAddBoth lte
  in (LTESucc ind)

lteSum : LTE l1 r1 -> LTE l2 r2 -> LTE (l1 + l2) (r1 + r2)
lteSum LTEZero lte2 {r1} {r2} =
  rewrite plusCommutative r1 r2 in
  lte2 `lteTransitive` lteAddRight r2
lteSum (LTESucc lte1') lte2 = LTESucc (lteSum lte1' lte2)

lteMultConst : LTE n m -> LTE (c * n) (c * m)
lteMultConst {c = Z} lte = LTEZero
lteMultConst {c = (S k)} {m} {n} lte =
  let ind = lteMultConst {c=k} lte
  in lteSum lte ind

elemStrictlySmallerThanBound : (n : Fin m) -> LT (finToNat n) m
elemStrictlySmallerThanBound FZ = LTESucc LTEZero
elemStrictlySmallerThanBound (FS x) =
  let ind = elemStrictlySmallerThanBound x
  in LTESucc ind

lteZeqZ : LTE a Z -> a = Z
lteZeqZ LTEZero = Refl

tightBound : LTE a b -> LTE b a -> a = b
tightBound LTEZero LTEZero = Refl
tightBound (LTESucc x) (LTESucc y) = eqSucc _ _ (tightBound x y)

splitLte : LTE a b -> Either (a = b) (LT a b)
splitLte {a = Z} {b = Z} LTEZero = Left Refl
splitLte {a = Z} {b = (S k)} LTEZero = Right (LTESucc LTEZero)
splitLte {a = (S _)} {b = Z} LTEZero impossible
splitLte {a = (S _)} {b = Z} (LTESucc _) impossible
splitLte {a = (S k)} {b = (S j)} (LTESucc lte') =
  case splitLte lte' of
    (Left eq) => Left (eqSucc _ _ eq)
    (Right lt) => Right (LTESucc lt)
