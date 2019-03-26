{-# LANGUAGE GADTs #-}

-- NAME -- Lane Gramling
-- KUID -- 2766765
-- Instructions for use:
--    1) Load in p3.hs
--    2) Input a for evaluation using any of the suitable
--       evaluators/type-checkers defined below



-- Imports for Monads

import Control.Monad

-- FAE AST and Type Definitions

data FAE where
  Num :: Int -> FAE
  Plus :: FAE -> FAE -> FAE
  Minus :: FAE -> FAE -> FAE
  Lambda :: String -> FAE -> FAE
  App :: FAE -> FAE -> FAE
  Id :: String -> FAE
  deriving (Show,Eq)

type Env = [(String,FAE)]

-- Lift an Int operator to FAEs
liftNum :: (Int -> Int -> Int) -> FAE -> FAE -> FAE
liftNum op (Num l) (Num r) = (Num (op l r)) -- op identifies the operator

-- Evaluate an FAE dynamically, using an Env with lookups and returning FAEs.
evalDynFAE :: Env -> FAE -> (Maybe FAE)
evalDynFAE e (Num n) = Just (Num n)
evalDynFAE e (Plus l r) = do { ll <- (evalDynFAE e l);
                               rr <- (evalDynFAE e r);
                               return (liftNum (+) ll rr)}
evalDynFAE e (Minus l r) = do { ll <- (evalDynFAE e l);
                                rr <- (evalDynFAE e r);
                                return (liftNum (-) ll rr)}
evalDynFAE e (Lambda i b) = Just (Lambda i b)
evalDynFAE e (App (Lambda i b) v) = evalDynFAE ((i,v):e) (b)
evalDynFAE e (Id i) = lookup i e
-- evalDynFAE _ _ = Nothing

data FAEValue where
  NumV :: Int -> FAEValue
  ClosureV :: String -> FAE -> Env' -> FAEValue
  deriving (Show,Eq)

type Env' = [(String,FAEValue)]


-- Lift an Int operator to FAEValue
liftNumToFAEVal :: (Int -> Int -> Int) -> FAEValue -> FAEValue -> FAEValue
liftNumToFAEVal op (NumV l) (NumV r) = (NumV (op l r)) -- op identifies the operator

-- Evaluate an FAE statically, using Closures and returning FAEValues.
evalStatFAE :: Env' -> FAE -> (Maybe FAEValue)
evalStatFAE e (Num n) = Just (NumV n)
evalStatFAE e (Plus l r) = do { ll <- (evalStatFAE e l);
                                rr <- (evalStatFAE e r);
                                return (liftNumToFAEVal (+) ll rr)}
evalStatFAE e (Minus l r) = do { ll <- (evalStatFAE e l);
                                 rr <- (evalStatFAE e r);
                                 return (liftNumToFAEVal (-) ll rr)}
evalStatFAE e (Lambda i b) = Just (ClosureV i b e)
evalStatFAE e (App (Lambda i b) v) = do { (ClosureV ii bb ee) <- evalStatFAE e (Lambda i b);
                                          vv <- evalStatFAE e v;
                                          evalStatFAE ((ii,vv):ee) (bb)}
-- evalStatFAE e (ClosureV i b e) = evalState
evalStatFAE e (Id i) = lookup i e

-- FBAE AST and Type Definitions

data FBAE where
  NumD :: Int -> FBAE
  PlusD :: FBAE -> FBAE -> FBAE
  MinusD :: FBAE -> FBAE -> FBAE
  LambdaD :: String -> FBAE -> FBAE
  AppD :: FBAE -> FBAE -> FBAE
  BindD :: String -> FBAE -> FBAE -> FBAE
  IdD :: String -> FBAE
  deriving (Show,Eq)

elabFBAE :: FBAE -> FAE
elabFBAE (NumD n) = (Num n)
elabFBAE (PlusD l r) = (Plus (elabFBAE l) (elabFBAE r))
elabFBAE (MinusD l r) = (Minus (elabFBAE l) (elabFBAE r))
elabFBAE (LambdaD i b) = (Lambda i (elabFBAE b))
elabFBAE (AppD f v) = (App (elabFBAE f) (elabFBAE v))
elabFBAE (BindD i v b) = (App (Lambda i (elabFBAE b)) (elabFBAE v))
elabFBAE (IdD i) = (Id i)
-- elabFBAE _ = (Num (-1))

evalFBAE :: Env' -> FBAE -> (Maybe FAEValue)
evalFBAE e expr = (evalStatFAE e (elabFBAE expr))
-- evalFBAE _ _ = Nothing

-- FBAEC AST and Type Definitions

data FBAEC where
  NumE :: Int -> FBAEC
  PlusE :: FBAEC -> FBAEC -> FBAEC
  MinusE :: FBAEC -> FBAEC -> FBAEC
  TrueE :: FBAEC
  FalseE :: FBAEC
  AndE :: FBAEC -> FBAEC -> FBAEC
  OrE :: FBAEC -> FBAEC -> FBAEC
  NotE :: FBAEC -> FBAEC
  IfE :: FBAEC -> FBAEC -> FBAEC -> FBAEC
  LambdaE :: String -> FBAEC -> FBAEC
  AppE :: FBAEC -> FBAEC -> FBAEC
  BindE :: String -> FBAEC -> FBAEC -> FBAEC
  IdE :: String -> FBAEC
  deriving (Show,Eq)

elabFBAEC :: FBAEC -> FAE
elabFBAEC (NumE n) = (Num n)
elabFBAEC (PlusE l r) = (Plus (elabFBAEC l) (elabFBAEC r))
elabFBAEC (MinusE l r) = (Minus (elabFBAEC l) (elabFBAEC r))
elabFBAEC (TrueE) = (Lambda "t" (Lambda ("f") (Id "t")))         -- lambda a in lambda b in a
elabFBAEC (FalseE) = (Lambda "t" (Lambda ("f") (Id "f")))        -- lambda a in lambda b in b
elabFBAEC (AndE a b) = (App (App (elabFBAEC a) (elabFBAEC b)) (elabFBAEC (a)))      -- lambda a in lambda b in a b a
elabFBAEC (OrE a b) = (App (App (elabFBAEC a) (elabFBAEC b)) (elabFBAEC (b)))       -- lambda a in lambda b in a a b
elabFBAEC (NotE a) = (App (App (elabFBAEC a) (elabFBAEC FalseE)) (elabFBAEC TrueE))       -- lambda a in a false true
elabFBAEC (IfE c t e) = (App (App (elabFBAEC c) (elabFBAEC t)) (elabFBAEC (e)))     -- lambda c in lambda t in lambda e in c t e
elabFBAEC (LambdaE i b) = (Lambda i (elabFBAEC b))
elabFBAEC (AppE f v) = (App (elabFBAEC f) (elabFBAEC v))
elabFBAEC (BindE i v b) = (App (Lambda i (elabFBAEC b)) (elabFBAEC v))
elabFBAEC (IdE i) = (Id i)
-- elabFBAEC _ = (Num (-1))

evalFBAEC :: FBAEC -> Maybe FAEValue
evalFBAEC expr = (evalStatFAE [] (elabFBAEC expr))
-- evalFBAEC _ = Nothing
