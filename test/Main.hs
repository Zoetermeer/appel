module Main where

import Control.Monad.State
import Data.List

type Id = String
type Value = Int
type EnvState = [(Id, Value)]

mtEnv :: EnvState
mtEnv = []

lookupId :: Id -> EnvState -> Maybe Value
lookupId id env = do
  result <- find (\(id', v) -> id' == id) env
  return $ snd result

updateEnv :: Id -> Value -> EnvState -> EnvState
updateEnv id v env = (id, v):env

data Exp =
    Num Int
  | Ref Id
  | Let Id Value Exp
  | Add Exp Exp
  deriving (Show)

eval :: Exp -> State EnvState (Maybe Value)
eval (Num v) = do return $ Just v
eval (Ref id) = do
  env <- get
  return $ lookupId id env

-- The above is equivalent to:
-- eval (Ref id) =
--    get >>= \env ->
--    return $ lookupId id env

eval (Let id v e) = do
  modify $ updateEnv id v
  eval e

-- eval (Let (Var id v) e) = do
--   modify ((:) (id, v))
--   eval e

eval (Add lhs rhs) = do
  maybeLv <- eval lhs
  maybeRv <- eval rhs
  return $ do { lv <- maybeLv; rv <- maybeRv; Just (lv + rv) }

main :: IO ()
main =
  putStrLn $ show $ runState (eval e) mtEnv
  where
    e = Let "foo" 43 (Let "bar" 44 (Add (Ref "bar") (Ref "foo")))














-- 
-- data ProgramState = PS [Int] deriving (Show)
-- 
-- foo :: Int -> String -> State ProgramState Int
-- foo x s = state $ \\st -> (42, PS [1, 2])
-- 
-- main :: IO ()
-- main =
--   putStrLn $ show $ runState (foo 2 "blah") (PS [])
