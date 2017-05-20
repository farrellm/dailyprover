module Problem1

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

lteZeqZ : (a : Nat) -> LTE a Z -> a = Z
lteZeqZ Z LTEZero = Refl

tightBound : (a : Nat) -> (b : Nat) -> LTE a b -> LTE b a -> a = b
tightBound Z Z LTEZero LTEZero = Refl
tightBound (S a') (S b') (LTESucc x) (LTESucc y) =
  let ind = tightBound a' b' x y
  in eqSucc a' b' ind

splitLte : (a : Nat) -> (b : Nat) -> LTE a b -> Either (a = b) (LT a b)
splitLte Z Z LTEZero = Left Refl
splitLte Z (S k) LTEZero = Right (LTESucc LTEZero)
splitLte (S a') (S b') (LTESucc lte') =
  case splitLte a' b' lte' of
    (Left eq) => Left (eqSucc a' b' eq)
    (Right lt) => Right (LTESucc lt)

boundedAbove : (n : Nat) -> (f : Nat -> Nat) -> (decr : Decr f) ->
               (a : Nat) -> (x : Nat) -> LTE a x ->
               LTE (f x) (f a)
boundedAbove n f decr a x lte =
  case splitLte a x lte of
    (Left eq) => rewrite eq in lteRefl
    (Right lt) =>
      let S x' = x
          LTESucc lte' = lt
          ind = boundedAbove n f decr a x' lte'
      in decr x' `lteTransitive` ind

boundedBelow : (n : Nat) -> (f : Nat -> Nat) -> (decr : Decr f) ->
               (a : Nat) -> (x : Nat) -> LTE x (n + a) ->
               LTE (f (n + a)) (f x)
boundedBelow Z f decr a x lte = boundedAbove Z f decr x a lte
boundedBelow n@(S n') f decr a x lte =
  let lte' = the (LTE x (S (n' + a)))
                 (rewrite plusCommutative n' a in
                  rewrite plusSuccRightSucc a n' in
                  rewrite plusCommutative a (S n') in
                  lte)
  in case splitLte x (S (n' + a)) lte' of
    (Left eq) => boundedAbove Z f decr x (S (n' + a)) lte'
    (Right lt) =>
      let LTESucc lte'' = lt
          ind = boundedBelow n' f decr a x lte''
      in decr (n' + a) `lteTransitive` ind

mkValley : (n : Nat) -> (f : Nat -> Nat) -> (decr : Decr f) ->
           (x : Nat) -> f x = f (n + x) ->
           (y : Nat) -> LTE x y -> LTE y (n + x) -> f y = f x
mkValley n f decr x prf y lteL lteU =
  let u = boundedAbove n f decr x y lteL
      l = boundedBelow n f decr x y lteU
  in tightBound (f y) (f x) u (rewrite prf in l)

decrValley_rec : (n : Nat) -> (f : Nat -> Nat) -> (decr : Decr f) ->
                 (x : Nat) -> (bound : Nat) -> (boundLte : LTE (f x) bound) ->
                 (a : Nat ** Valley f n a)
decrValley_rec n f decr x Z boundLte =
  let boundLteN = decrN n f decr x
      boundLteN' = lteTransitive boundLteN boundLte
      xEqZ = lteZeqZ (f x) boundLte
      xNEqZ = lteZeqZ (f (n + x)) boundLteN'
      xEqNx = xEqZ `trans` sym xNEqZ
  in (x ** mkValley n f decr x xEqNx)

decrValley_rec n f decr x bound@(S bound') boundLte =
  case splitLte (f x) (S bound') boundLte of
    (Right (LTESucc boundLte')) => decrValley_rec n f decr x bound' boundLte'
    (Left boundEq) =>
      let boundLteN = decrN n f decr x
      in case splitLte (f (n + x)) (f x) boundLteN of
              (Right boundLtN) =>
                let boundLteN' = fromLteSucc (boundLtN `lteTransitive` boundLte)
                in decrValley_rec n f decr (n + x) bound' boundLteN'
              (Left boundEqN) => (x ** mkValley n f decr x (sym boundEqN))

decrValley : (n : Nat) -> (f : Nat -> Nat) -> Decr f -> (x : Nat ** Valley f n x)
decrValley n f decr = decrValley_rec n f decr Z (f Z) lteRefl
