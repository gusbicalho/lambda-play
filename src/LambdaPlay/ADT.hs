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
  deriving (Eq, Show)

infixl 7 :|
infixr 5 :.

type Reduction = (Env, Lambda) -> Maybe Lambda

reduce :: Reduction -> Reduction
reduce apply = reduceTerm
  where
    reduceTerm :: Reduction
    reduceTerm s = reduceClosed s <|> resolveV s <|> reduceFn s <|> reduceArg s <|> apply s
    reduceClosed :: Reduction
    reduceClosed (_, Closed _ c@(Closed _ _)) = Just c
    reduceClosed (env, Closed closedEnv f@(_ :. _) :| arg) =
      Just $ Closed closedEnv (f :| Closed env arg)
    reduceClosed (_, Closed env v@(Var sym)) =
      case resolveSym sym env of
        Nothing  -> Just v
        Just val -> Just val
    reduceClosed (_, Closed env t) = Closed env <$> reduceTerm (env, t)
    reduceClosed _ = Nothing
    resolveV :: Reduction
    resolveV (env, Var sym) = resolveSym sym env
    resolveV _ = Nothing
    reduceFn :: Reduction
    reduceFn (env, f :| arg) = fmap (:| arg) (reduceTerm (env, f))
    reduceFn _ = Nothing
    reduceArg :: Reduction
    reduceArg (env, f :| arg) = fmap (f :|) (reduceTerm (env, arg))
    reduceArg _ = Nothing

applyByValue :: Reduction
applyByValue (env, (argName :. body) :| arg) =
  case arg of
    f@(_ :. _)            -> Just $ Closed (setSym argName (Closed env f) env) body
    f@(Closed _ (_ :. _)) -> Just $ Closed (setSym argName (Closed env f) env) body
    v@(Var _)             -> Just $ Closed (setSym argName (Closed env v) env) body
    v@(Closed _ (Var _))  -> Just $ Closed (setSym argName (Closed env v) env) body
    _ -> Nothing
applyByValue _ = Nothing

applyByName :: Reduction
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
one = F :. Var F
inc = N :. F :. X :. Var F :| (Var N :| Var F :| Var X)
two = inc :| one
three = inc :| two
plus = N :. M :. Var N :| inc :| Var M
nil = F :. Z :. Var Z
cons = X :. L :. F :. Z :. Var F :| Var X :| (Var L :| Var F :| Var Z)
lAny = L :. Var L :| lOr :| lFalse
lAll = L :. Var L :| lAnd :| lTrue

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
            ]

tests apply = map testOne testCases
  where testOne (expr, expected)
          | expected == actual = Right ()
          | otherwise = Left (expr, expected, actual)
          where actual = reduceEnd apply [] expr
