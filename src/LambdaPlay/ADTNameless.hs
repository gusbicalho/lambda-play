module LambdaPlay.ADTNameless where

import Data.List (tails)

data NamedLambda = Var String
                 | NamedLambda :| NamedLambda
                 | String :. NamedLambda
  deriving (Eq, Show)
infixl 7 :|
infixr 5 :.

data Lambda = V Int
            | App Lambda Lambda
            | Abs Lambda
  deriving (Eq, Show)

newtype NamingContext = NC [String]
  deriving (Eq, Show)

bindSym :: String -> NamingContext -> NamingContext
bindSym sym (NC bindings) = NC (sym : bindings)

resolveName :: NamingContext -> String -> (NamingContext, Int)
resolveName nc@(NC bindings) sym = bound bindings 0
  where
    bound :: [String] -> Int -> (NamingContext, Int)
    bound []     i = (NC $ bindings ++ [sym], i)
    bound (s:ss) i | s == sym  = (nc, i)
                   | otherwise = bound ss (i + 1)

removeNames' :: NamingContext -> NamedLambda -> (NamingContext, Lambda)
removeNames' nameCtx = \case
  Var s  -> V <$> (resolveName nameCtx s)
  l :| m -> let (nameCtx',  l') = removeNames' nameCtx l
                (nameCtx'', m') = removeNames' nameCtx' m
            in (nameCtx'', App l' m')
  s :. l -> Abs <$> removeNames' (bindSym s nameCtx) l

removeNames :: NamedLambda -> Lambda
removeNames = snd . removeNames' (NC [])

nth :: (Num t, Ord t) => t -> [a] -> Maybe a
nth i (x:xs) | i == 0 = Just x
             | i > 0  = nth (i - 1) xs
nth _ _ = Nothing

strs :: [String]
strs = prefixes ++ (strs >>= \s -> map (s ++) prefixes)
  where prefixes = map (:[]) "abcd"

newName :: NamingContext -> String
newName (NC bindings) = head . filter unbound $ strs
  where unbound s = all (s /=) bindings

resolveNum :: NamingContext -> Int -> (NamingContext, String)
resolveNum nc@(NC bindings) i = case nth i bindings of
    Just s -> (nc, s)
    Nothing -> (NC $ bindings ++ [newName'], newName')
  where
    newName' = newName nc

pushNewName :: NamingContext -> (NamingContext, String)
pushNewName nc@(NC bindings) = (NC $ name : bindings, name)
  where name = newName nc

restoreNames' :: NamingContext -> Lambda -> (NamingContext, NamedLambda)
restoreNames' nameCtx = \case
  V i     -> Var <$> resolveNum nameCtx i
  App l m -> let (nameCtx',  l') = restoreNames' nameCtx l
                 (nameCtx'', m') = restoreNames' nameCtx' m
             in (nameCtx'', l' :| m')
  Abs l   -> let (nameCtx', name) = pushNewName nameCtx
                 (_, body) = restoreNames' nameCtx' l
             in (nameCtx, name :. body)

restoreNames = snd . restoreNames' (NC [])

-- Examples

identity, lTrue, lFalse, lNot :: NamedLambda
identity = "X" :. Var "X"
lTrue = "X" :. "Y" :. Var "X"
lFalse = "X" :. "Y" :. Var "Y"
lNot = "Z" :. Var "Z" :| lFalse :| lTrue

roundTrip :: Lambda -> Bool
roundTrip l = l == removeNames (restoreNames l)
