module Problem1

%default total

record DecFun (f : Nat -> Nat) where
  constructor MkDecreasingFunction
    decreasing : (a : Nat) -> (b : Nat) -> LTE (f a) b -> LTE (f (S a)) b

eqSucc' : (a = b) -> (S a = S b)
eqSucc' {a} {b} prf = eqSucc a b prf

splitLte : LTE a b -> Either (a = b) (LT a b)
splitLte {b = Z} LTEZero = Left Refl
splitLte {b = (S k)} LTEZero = Right (LTESucc LTEZero)
splitLte (LTESucc x) =
  case splitLte x of
    Left eq => Left (eqSucc' eq)
    Right lte' => Right (LTESucc lte')

tightenLt : LT a b -> (c ** LTE a c)
tightenLt {a = a} {b = Z} lt = void (succNotLTEzero lt)
tightenLt {a = a} {b = (S c)} lt =
  let lte = fromLteSucc lt
  in (c ** lte)

lteZeqZ : LTE a Z -> a = Z
lteZeqZ LTEZero = Refl

argAddNBound : DecFun f -> LTE (f a) b -> LTE (f (a+n)) b
argAddNBound {n = Z} {a} dec lte =
  rewrite plusZeroRightNeutral a in
  lte
argAddNBound {n = (S k)} {a} {b} dec lte =
  let ind = argAddNBound dec lte {n=k} {a=a}
      lte' = (decreasing dec) (a+k) b ind
  in rewrite sym (plusSuccRightSucc a k) in
     lte'

nValleyRec : (a : Nat) -> (bound : Nat) ->
             (lteBound : LTE (f a) bound) ->
             (dec : DecFun f) ->
             (b : Nat ** (f b) = (f (plus b n)))
nValleyRec {n} a Z lteBound dec =
  let aEqZ = lteZeqZ lteBound
      lteN = argAddNBound dec lteBound {a=a} {n=n}
      nEqZ = lteZeqZ lteN
  in (a ** trans aEqZ (sym nEqZ))
nValleyRec {n} a bound@(S bound') lteBound dec =
  case splitLte lteBound of
    (Right lt) =>
      let (LTESucc lteBound') = lt
      in nValleyRec a bound' lteBound' dec
    (Left eq) =>
      let lteN = argAddNBound dec lteBound {a=a} {n=n}
      in case splitLte lteN of
              (Left eqN) => (a ** trans eq (sym eqN))
              (Right ltN) =>
                let (LTESucc lteBound') = ltN
                in nValleyRec (a + n) bound' lteBound' dec

NValley : (dec : DecFun f) ->
          (a : Nat ** (f a) = (f (a+n)))
NValley {f} dec =
  nValleyRec Z (f Z) lteRefl dec
