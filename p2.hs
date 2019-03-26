{-# LANGUAGE GADTs,FlexibleContexts #-}


-- NAME -- Lane Gramling
-- KUID -- 2766765
-- Instructions for use:
--    1) Load in p2.hs
--    2) Input a BBAE for evaluation using any of the suitable
--       evaluators/type-checkers defined below

-- Imports for Monads

import Control.Monad

-- BBAE AST and Type Definitions

data TBBAE where
  TNum :: TBBAE
  TBool :: TBBAE
  deriving (Show,Eq)

data BBAE where
  Num :: Int -> BBAE
  Plus :: BBAE -> BBAE -> BBAE
  Minus :: BBAE -> BBAE -> BBAE
  Bind :: String -> BBAE -> BBAE -> BBAE
  Id :: String -> BBAE
  Boolean :: Bool -> BBAE
  And :: BBAE -> BBAE -> BBAE
  Leq :: BBAE -> BBAE -> BBAE
  IsZero :: BBAE -> BBAE
  If :: BBAE -> BBAE -> BBAE -> BBAE
  deriving (Show,Eq)

type Env = [(String,BBAE)]

type Cont = [(String,TBBAE)]


-- Lift Functions

-- Lift an Int operator to BBAEs
liftNum :: (Int -> Int -> Int) -> BBAE -> BBAE -> BBAE
liftNum op (Num l) (Num r) = (Num (op l r)) -- op identifies the operator

-- Lift an Int operator with Bool results to BBAEs
liftNumToBool :: (Int -> Int -> Bool) -> BBAE -> BBAE -> BBAE
liftNumToBool op (Num l) (Num r) = (Boolean (op l r)) -- op identifies the operator

-- Lift a Boolean Operator with Bool results to BBAEs
liftBool :: (Bool -> Bool -> Bool) -> BBAE -> BBAE -> BBAE
liftBool op (Boolean l) (Boolean r) = (Boolean (op l r)) -- op identifies the operator



subst :: String -> BBAE -> BBAE -> BBAE
subst _ _ (Num x) = (Num x)
subst i v (Plus l r) = (Plus (subst i v l) (subst i v r))
subst i v (Minus l r) = (Minus (subst i v l) (subst i v r))
subst i v (And l r) = (And (subst i v l) (subst i v r))
subst i v (Leq l r) = (Leq (subst i v l) (subst i v r))
subst i v (IsZero n) = (IsZero (subst i v n))
subst i v (If c t e) = (If (subst i v c) (subst i v t) (subst i v e))
subst i v (Id ii) = if i==ii then v else (Id ii)
subst i v (Bind ii vv bb) = if i==ii
                            then (Bind ii (subst i v vv) bb)
                            else (Bind ii (subst i v vv) (subst i v bb))

evalS :: BBAE -> (Maybe BBAE)
evalS (Num n) = if n >= 0 then Just (Num n) else Nothing
evalS (Boolean b) = Just (Boolean b)
evalS (Plus l r) = do a1 <- (evalS l)
                      a2 <- (evalS r)
                      return (liftNum (+) a1 a2)
evalS (Minus l r) = do a1 <- (evalS l)
                       a2 <- (evalS r)
                       case a1 of
                         (Num a11) -> case a2 of -- l-r<=0 case
                                        (Num a22) ->
                                            if ((a11-a22)<0) then Nothing else return (liftNum (-) a1 a2)
evalS (And l r) = do a1 <- (evalS l) -- Boolean Operands
                     a2 <- (evalS r)
                     return (liftBool (&&) a1 a2)
evalS (Leq l r) = do a1 <- (evalS l) -- Numeric Operands, Boolean Result
                     a2 <- (evalS r)
                     return (liftNumToBool (<=) a1 a2)
evalS (IsZero n) = do n1 <- (evalS n) -- Numeric Operand, Boolean Result
                      return (liftNumToBool (==) n1 (Num 0))
evalS (If c t e) = do (Boolean c1) <- (evalS c)
                      if c1 then evalS t else evalS e
evalS (Bind i v b) = do { vv <- (evalS v);
                          (evalS (subst i vv b))}
evalS _ = Nothing



evalM :: Env -> BBAE -> (Maybe BBAE)
evalM env (Num x) = (Just (Num x))
evalM env (Boolean b) = (Just (Boolean b))
evalM env (Plus l r) = do a1 <- (evalM env l)
                          a2 <- (evalM env r)
                          return (liftNum (+) a1 a2)
evalM env (Minus l r) = do a1 <- (evalM env l)
                           a2 <- (evalM env r)
                           return (liftNum (-) a1 a2)
evalM env (And l r) = do a1 <- (evalM env l)
                         a2 <- (evalM env r)
                         return (liftBool (&&) a1 a2)
evalM env (Leq l r) = do a1 <- (evalM env l)
                         a2 <- (evalM env r)
                         return (liftNumToBool (<=) a1 a2)
evalM env (IsZero n) = do nn <- (evalM env n)
                          return (liftNumToBool (==) nn (Num 0))
evalM env (Bind i v b) = do vv <- (evalM env v)
                            evalM ((i,vv):env) b
evalM env (Id id) = lookup id env
evalM _ _ = Nothing

testBBAE :: BBAE -> Bool
testBBAE expr = (evalS expr) == (evalM [] expr)
-- testBBAE _ = True

typeofM :: Cont -> BBAE -> (Maybe TBBAE)
typeofM cont (Num n) = Just TNum
typeofM cont (Boolean b) = Just TBool
typeofM cont (Plus l r) = do TNum <- (typeofM cont l)
                             TNum <- (typeofM cont r)
                             return TNum
typeofM cont (Minus l r) = do TNum <- (typeofM cont l)
                              TNum <- (typeofM cont r)
                              return TNum
typeofM cont (And l r) = do TBool <- (typeofM cont l) -- Boolean Operands
                            TBool <- (typeofM cont r)
                            return TBool
typeofM cont (Leq l r) = do TNum <- (typeofM cont l) -- Numeric Operands
                            TNum <- (typeofM cont r)
                            return TBool
typeofM cont (IsZero n) = do TNum <- (typeofM cont n) -- Numeric Operand
                             return TBool
typeofM cont (If c t e) = do c1 <- (typeofM cont c)
                             t1 <- (typeofM cont t)
                             e1 <- (typeofM cont e) -- Confirm then/else types match
                             if c1==TBool && t1==e1 then return t1 else Nothing
typeofM cont (Bind i v b) = do vv <- (typeofM cont v)
                               typeofM ((i,vv):cont) b
typeofM cont (Id id) = lookup id cont
-- typeofM _ _ = Nothing

evalT :: BBAE -> (Maybe BBAE)
evalT expr = case (typeofM [] expr) of
                   Just _ -> (evalM [] expr)
                   Nothing -> Nothing
-- evalT _ = Nothing
