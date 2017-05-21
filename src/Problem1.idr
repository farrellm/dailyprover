module Problem1

import Common.Lte

%default total

Decr : (Nat -> Nat) -> Type
Decr f = (x : Nat) -> LTE (f (S x)) (f x)

Valley : (Nat -> Nat) -> Nat -> Nat -> Type
Valley f n x = (y : Nat) -> LTE x y -> LTE y (n+x) -> f y = f x

decrN : (n : Nat) -> (f : Nat -> Nat) -> Decr f -> (x : Nat) ->
        LTE (f (n + x)) (f x)
decrN Z f decr x = lteRefl
decrN (S n') f decr x =
  let ind = decrN n' f decr x
      decrLte = decr (n' + x)
  in lteTransitive decrLte ind

boundedAbove : (decr : Decr f) -> (a : Nat) -> (x : Nat) -> LTE a x ->
               LTE (f x) (f a)
boundedAbove decr a x lte =
  case splitLte lte of
    (Left eq) => rewrite eq in lteRefl
    (Right lt) =>
      let S x' = x
          lte' = fromLteSucc lt
          ind = boundedAbove decr a x' lte'
      in decr x' `lteTransitive` ind

boundedBelow : (n : Nat) -> (decr : Decr f) ->
               (a : Nat) -> (x : Nat) -> LTE x (n + a) ->
               LTE (f (n + a)) (f x)
boundedBelow Z decr a x lte = boundedAbove decr x a lte
boundedBelow n@(S n') decr a x lte =
  case splitLte lte of
    (Left eq) => boundedAbove decr x (S (n' + a)) lte
    (Right lt) =>
      let ind = boundedBelow n' decr a x (fromLteSucc lt)
      in decr (n' + a) `lteTransitive` ind

mkValley : (n : Nat) -> (f : Nat -> Nat) -> (decr : Decr f) ->
           (x : Nat) -> f x = f (n + x) ->
           (y : Nat) -> LTE x y -> LTE y (n + x) -> f y = f x
mkValley n f decr x prf y lteL lteU =
  let u = boundedAbove decr x y lteL
      l = boundedBelow n decr x y lteU
  in tightBound u (rewrite prf in l)

decrValley_rec : (n : Nat) -> (f : Nat -> Nat) -> (decr : Decr f) ->
                 (x : Nat) -> (bound : Nat) -> (boundLte : LTE (f x) bound) ->
                 (a : Nat ** Valley f n a)
decrValley_rec n f decr x Z boundLte =
  let boundLteN = decrN n f decr x
      boundLteN' = lteTransitive boundLteN boundLte
      xEqZ = lteZeqZ boundLte
      xNEqZ = lteZeqZ boundLteN'
      xEqNx = xEqZ `trans` sym xNEqZ
  in (x ** mkValley n f decr x xEqNx)

decrValley_rec n f decr x bound@(S bound') boundLte =
  case splitLte boundLte of
    (Right (LTESucc boundLte')) => decrValley_rec n f decr x bound' boundLte'
    (Left boundEq) =>
      let boundLteN = decrN n f decr x
      in case splitLte boundLteN of
              (Right boundLtN) =>
                let boundLteN' = fromLteSucc (boundLtN `lteTransitive` boundLte)
                in decrValley_rec n f decr (n + x) bound' boundLteN'
              (Left boundEqN) => (x ** mkValley n f decr x (sym boundEqN))

decrValley : (n : Nat) -> (f : Nat -> Nat) -> Decr f -> (x : Nat ** Valley f n x)
decrValley n f decr = decrValley_rec n f decr Z (f Z) lteRefl
