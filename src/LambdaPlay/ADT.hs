module LambdaPlay.ADT where

import GHC.IO.Unsafe (unsafePerformIO)

import Control.Applicative ((<|>))

data Symbol = A | B | C | F | L | M | N | X | Y | Z
  deriving (Eq, Show)

data Lambda = V Symbol
            | Lambda :| Lambda
            | Symbol :. Lambda
  deriving (Eq, Show)

infixl 7 :|
infixr 5 :.

lTrue = X :. Y :. V X
lFalse = X :. Y :. V Y
lNot = Z :. V Z :| lFalse :| lTrue
lOr = A :. B :. X :. Y :. V A :| V X :| (V B :| V X :| V Y)
lAnd = A :. B :. X :. Y :. V A :| (V B :| V X :| V Y) :| V Y
pair = X :. Y :. Z :. V Z :| V X :| V Y
one = F :. V F
inc = N :. F :. X :. V F :| (V N :| V F :| V X)
two = inc :| one
three = inc :| two
plus = N :. M :. V N :| inc :| V M
nil = F :. Z :. V Z
cons = X :. L :. F :. Z :. V F :| V X :| (V L :| V F :| V Z)
lAny = L :. V L :| lOr :| lFalse
lAll = L :. V L :| lAnd :| lTrue

ttt = cons :| lTrue  :| (cons :| lTrue  :| (cons :| lTrue  :| nil))
tft = cons :| lTrue  :| (cons :| lFalse :| (cons :| lTrue  :| nil))
ftf = cons :| lFalse :| (cons :| lTrue  :| (cons :| lFalse :| nil))
fff = cons :| lFalse :| (cons :| lFalse :| (cons :| lFalse :| nil))

type Reduction = Lambda -> Maybe Lambda

replaceSym :: Symbol -> Lambda -> Lambda -> Lambda
replaceSym sym val e@(V sym') | sym == sym' = val
                              | otherwise   = e
replaceSym sym val (f :| arg) = replaceSym sym val f :| replaceSym sym val arg
replaceSym sym val e@(argSym :. body) | sym == argSym = e
                                      | otherwise     = argSym :. replaceSym sym val body

reduce :: Reduction -> Reduction
reduce apply = reduceTerm
  where
    reduceTerm :: Reduction
    reduceTerm s = apply s <|> reduceFn s <|> reduceArg s
    reduceFn :: Reduction
    reduceFn (f :| arg) = fmap (:| arg) (reduceTerm f)
    reduceFn _ = Nothing
    reduceArg :: Reduction
    reduceArg (f :| arg) = fmap (f :|) (reduceTerm arg)
    reduceArg _ = Nothing

applyByValue :: Reduction
applyByValue ((argName :. body) :| arg) =
  case arg of
    f@(_ :. _) -> Just $ replaceSym argName f body
    v@(V _)    -> Just $ replaceSym argName v body
    _ -> Nothing
applyByValue _ = Nothing

applyByName :: Reduction
applyByName ((argName :. body) :| arg) = Just $ replaceSym argName arg body
applyByName _ = Nothing

reduceAll apply expr = reverse $ go [expr] expr
  where go acc expr = case reduce apply expr of
          Nothing    -> acc
          Just expr' -> go (expr' : acc) expr'

reduceEnd apply = last . reduceAll apply

reduceCount apply expr = let reds = reduceAll apply expr
                         in (length reds, last reds)
