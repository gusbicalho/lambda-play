{-# OPTIONS_GHC -fno-warn-missing-signatures #-}
module LambdaPlay.ADT where

import GHC.IO.Unsafe (unsafePerformIO)

import Control.Applicative ((<|>))

data Symbol = A | B | C | F | L | M | N | X | Y | Z
  deriving (Eq, Show)

type Env = [(Symbol, Lambda)]
resolveSym :: Symbol -> Env -> Maybe Lambda
resolveSym = lookup
setSym :: Symbol -> Lambda -> Env -> Env
setSym sym val [] = [(sym, val)]
setSym sym val (e@(sym', _): env) | sym == sym' = (sym, val) : env
                                  | otherwise   = e : setSym sym val env

data Lambda = Var Symbol
            | Lambda :| Lambda
            | Symbol :. Lambda
            | Closed Env Lambda
            | Zero
            | Succ Lambda
  deriving (Eq, Show)

infixl 7 :|
infixr 5 :.

type Reduction = (Env, Lambda) -> Maybe Lambda

reduce :: Reduction -> Reduction
reduce apply = reduceTerm
  where
    reduceTerm :: Reduction
    reduceTerm s =
      apply s
      <|> reduceClosed s
      <|> reduceFn s
      <|> reduceArg s
      <|> resolveV s
      <|> reduceSucc s
    reduceClosed :: Reduction
    reduceClosed (_, Closed _ c@(Closed _ _)) = Just c
    reduceClosed (env, Closed closedEnv f@(_ :. _) :| arg) =
      Just $ Closed closedEnv (f :| Closed env arg)
    reduceClosed (_, Closed _ Zero) = Just Zero
    reduceClosed (_, Closed env (Succ t)) =
      Just $ Succ (Closed env t)
    reduceClosed (_, Closed env v@(Var sym)) =
      case resolveSym sym env of
        Nothing  -> Just v
        Just val -> Just val
    reduceClosed (_, Closed env t) = Closed env <$> reduceTerm (env, t)
    reduceClosed _ = Nothing
    reduceSucc :: Reduction
    reduceSucc (env, Succ n) = Succ <$> reduceTerm (env, n)
    reduceSucc _ = Nothing
    resolveV :: Reduction
    resolveV (env, Var sym) = resolveSym sym env
    resolveV _ = Nothing
    reduceFn :: Reduction
    reduceFn (env, f :| arg) = fmap (:| arg) (reduceTerm (env, f))
    reduceFn _ = Nothing
    reduceArg :: Reduction
    reduceArg (env, f :| arg) = fmap (f :|) (reduceTerm (env, arg))
    reduceArg _ = Nothing

isNormal :: Lambda -> Bool
isNormal f@(_ :. _) = True
isNormal v@(Var _)  = True
isNormal Zero       = True
isNormal (Succ t)   = isNormal t
isNormal _          = False

closedValueIs :: (Lambda -> Bool) -> Lambda -> Bool
closedValueIs pred (Closed _ t) = pred t
closedValueIs _ _ = False

applyByValue :: Reduction
applyByValue (env, (argName :. body) :| arg)
  | isNormal arg = Just $ Closed (setSym argName (Closed env arg) env) body
  | closedValueIs isNormal arg = Just $ Closed (setSym argName arg env) body
applyByValue _ = Nothing

applyByName :: Reduction
applyByName (env, (argName :. body) :| arg@(Closed _ _)) =
  Just $ Closed (setSym argName arg env) body
applyByName (env, (argName :. body) :| arg) =
  Just $ Closed (setSym argName (Closed env arg) env) body
applyByName _ = Nothing

reduceAll :: Reduction -> Env -> Lambda -> [Lambda]
reduceAll apply env e = reverse $ go [e] e
  where go acc expr = case reduce apply (env, expr) of
          Nothing    -> acc
          Just expr' -> go (expr' : acc) expr'

reduceEnd :: Reduction -> Env -> Lambda -> Lambda
reduceEnd apply env = last . reduceAll apply env

eval :: Reduction -> Lambda -> Lambda
eval apply = reduceEnd apply []

reduceCount :: Reduction -> Env -> Lambda -> (Int, Lambda)
reduceCount apply env expr = let reds = reduceAll apply env expr
                             in (length reds, last reds)

-- Tests

identity = X :. Var X
lTrue = X :. Y :. Var X
lFalse = X :. Y :. Var Y
lNot = Z :. Var Z :| lFalse :| lTrue
lOr = A :. B :. X :. Y :. Var A :| Var X :| (Var B :| Var X :| Var Y)
lAnd = A :. B :. X :. Y :. Var A :| (Var B :| Var X :| Var Y) :| Var Y
pair = X :. Y :. Z :. Var Z :| Var X :| Var Y
zero = F :. A :. Var A
one = F :. A :. Var F :| Var A
inc = N :. F :. X :. Var F :| (Var N :| Var F :| Var X)
two = inc :| one
three = inc :| two
plus = N :. M :. Var N :| inc :| Var M
times = N :. M :. Var N :| (plus :| Var M) :| zero
power = N :. M :. Var N :| (times :| Var M) :| one
nil = F :. Z :. Var Z
cons = X :. L :. F :. Z :. Var F :| Var X :| (Var L :| Var F :| Var Z)
lAny = L :. Var L :| lOr :| lFalse
lAll = L :. Var L :| lAnd :| lTrue
applySucc = X :. Succ (Var X)
toSuccZero = N :. Var N :| applySucc :| Zero

ttt = cons :| lTrue  :| (cons :| lTrue  :| (cons :| lTrue  :| nil))
tft = cons :| lTrue  :| (cons :| lFalse :| (cons :| lTrue  :| nil))
ftf = cons :| lFalse :| (cons :| lTrue  :| (cons :| lFalse :| nil))
fff = cons :| lFalse :| (cons :| lFalse :| (cons :| lFalse :| nil))

testCases = [ (lAny :| ttt :| Var A :| Var B, Var A)
            , (lAny :| tft :| Var A :| Var B, Var A)
            , (lAny :| ftf :| Var A :| Var B, Var A)
            , (lAny :| fff :| Var A :| Var B, Var B)
            , (lAll :| ttt :| Var A :| Var B, Var A)
            , (lAll :| tft :| Var A :| Var B, Var B)
            , (lAll :| ftf :| Var A :| Var B, Var B)
            , (lAll :| fff :| Var A :| Var B, Var B)
            , (toSuccZero :| zero, Zero)
            , (toSuccZero :| one, Succ Zero)
            , (toSuccZero :| two, Succ (Succ Zero))
            , (toSuccZero :| (inc :| zero), Succ                 Zero)
            , (toSuccZero :| (inc :|  one), Succ . Succ        $ Zero)
            , (toSuccZero :| (inc :|  two), Succ . Succ . Succ $ Zero)
            , (toSuccZero :| (plus :| zero :|  zero),                                    Zero)
            , (toSuccZero :| (plus :| zero :|   one),                             Succ $ Zero)
            , (toSuccZero :| (plus :|  one :|  zero),                             Succ $ Zero)
            , (toSuccZero :| (plus :|  one :|   one),                      Succ . Succ $ Zero)
            , (toSuccZero :| (plus :|  two :|  zero),                      Succ . Succ $ Zero)
            , (toSuccZero :| (plus :| zero :|   two),                      Succ . Succ $ Zero)
            , (toSuccZero :| (plus :| two  :| three), Succ . Succ . Succ . Succ . Succ $ Zero)
            , (toSuccZero :| (times :| zero :|  zero),                                           Zero)
            , (toSuccZero :| (times :| zero :|   one),                                           Zero)
            , (toSuccZero :| (times :| zero :|   two),                                           Zero)
            , (toSuccZero :| (times :|  one :|  zero),                                           Zero)
            , (toSuccZero :| (times :|  two :|  zero),                                           Zero)
            , (toSuccZero :| (times :|  one :|   one),                                    Succ $ Zero)
            , (toSuccZero :| (times :|  one :|   two),                             Succ . Succ $ Zero)
            , (toSuccZero :| (times :|  two :|   one),                             Succ . Succ $ Zero)
            , (toSuccZero :| (times :|  two :| three), Succ . Succ . Succ . Succ . Succ . Succ $ Zero)
            , (toSuccZero :| (cons :| one :| (cons :| two :| (cons :| three :| nil)) :| plus :| zero)
              ,Succ . Succ . Succ . Succ . Succ . Succ $ Zero)
            , (toSuccZero :| (cons :| one :| (cons :| two :| (cons :| three :| nil)) :| times :| one)
              ,Succ . Succ . Succ . Succ . Succ . Succ $ Zero)
            ]

tests apply = map (testOne apply) testCases

testOne apply (expr, expected)
  | expected == actual = Right ()
  | otherwise = Left (expr, expected, actual)
  where actual = reduceEnd apply [] expr
