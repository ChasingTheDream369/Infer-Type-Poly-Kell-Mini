module MinHS.TyInfer where

import qualified MinHS.Env as E
import MinHS.Syntax
import MinHS.Subst
import MinHS.TCMonad

import Data.Monoid (Monoid (..), (<>))
import Data.Foldable (foldMap)
import Data.List (nub, union, (\\))

primOpType :: Op -> QType
primOpType Gt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ge   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Lt   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Le   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Eq   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Ne   = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Bool)
primOpType Neg  = Ty $ Base Int `Arrow` Base Int
primOpType Fst  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "a"
primOpType Snd  = Forall "a" $ Forall "b" $ Ty $ (TypeVar "a" `Prod` TypeVar "b") `Arrow` TypeVar "b"
primOpType _    = Ty $ Base Int `Arrow` (Base Int `Arrow` Base Int)

constType :: Id -> Maybe QType
constType "True"  = Just $ Ty $ Base Bool
constType "False" = Just $ Ty $ Base Bool
constType "()"    = Just $ Ty $ Base Unit
constType "Pair"  = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "b" `Arrow` (TypeVar "a" `Prod` TypeVar "b"))
constType "Inl"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "a" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType "Inr"   = Just
                  $ Forall "a"
                  $ Forall "b"
                  $ Ty
                  $ TypeVar "b" `Arrow` (TypeVar "a" `Sum` TypeVar "b")
constType _       = Nothing

type Gamma = E.Env QType

initialGamma :: Gamma
initialGamma = E.empty

tv :: Type -> [Id]
tv = tv'
 where
   tv' (TypeVar x) = [x]
   tv' (Prod  a b) = tv a `union` tv b
   tv' (Sum   a b) = tv a `union` tv b
   tv' (Arrow a b) = tv a `union` tv b
   tv' (Base c   ) = []

tvQ :: QType -> [Id]
tvQ (Forall x t) = filter (/= x) $ tvQ t
tvQ (Ty t) = tv t

tvGamma :: Gamma -> [Id]
tvGamma = nub . foldMap tvQ

infer :: Program -> Either TypeError Program
infer program = do (p',tau, s) <- runTC $ inferProgram initialGamma program
                   return p'

unquantify :: QType -> TC Type
{-
Normally this implementation would be possible:
unquantify (Ty t) = return t
unquantify (Forall x t) = do x' <- fresh
                             unquantify (substQType (x =:x') t)
However as our "fresh" names are not checked for collisions with names bound in the type
we avoid capture entirely by first replacing each bound
variable with a guaranteed non-colliding variable with a numeric name,
and then substituting those numeric names for our normal fresh variables
-}

unquantify = unquantify' 0 emptySubst
unquantify' :: Int -> Subst -> QType -> TC Type
unquantify' i s (Ty t) = return $ substitute s t
unquantify' i s (Forall x t) = do x' <- fresh
                                  unquantify' (i + 1)
                                              ((show i =: x') <> s)
                                              (substQType (x =:TypeVar (show i)) t)



subUnify :: Type -> Type -> Type -> Type -> TC Subst
subUnify t11 t21 t12 t22 = do
  s <- unify t11 t21
  s' <- unify (substitute s t12) (substitute s t22)
  return (s <> s')


unify :: Type -> Type -> TC Subst
unify (TypeVar v1) (TypeVar v2)
  | v1 == v2 = return emptySubst
  | otherwise = return (v1 =: TypeVar v2)
unify (Base p1) (Base p2)
  | p1 == p2 = return emptySubst    --If p1 /= p2 then nothing is returned
unify (Prod t11 t12) (Prod t21 t22) = subUnify t11 t21 t12 t22
unify (Arrow t11 t12) (Arrow t21 t22) = subUnify t11 t21 t12 t22
unify (Sum t11 t12) (Sum t21 t22) = subUnify t11 t21 t12 t22
--Use elem to check if v already is in t. elem requires t to be a list, so we must use tv t.
unify (TypeVar v) t
  | elem v (tv t) = typeError (OccursCheckFailed v t)  
  | otherwise = return (v =: t)
unify t (TypeVar v) = unify (TypeVar v) t
unify t1 t2 = typeError (TypeMismatch t1 t2)



generalise :: Gamma -> Type -> QType
generalise g t = 
  let free = tv t \\ tvGamma g
  in foldr Forall (Ty t) free


inferProgram :: Gamma -> Program -> TC (Program, Type, Subst)

inferProgram gama [Bind name _ [] progExpr] = do 
  (expr, exptype, subExp) <- inferExp gama progExpr 
  case generalise gama (substitute subExp exptype) of 
    Ty typeSet -> return ([Bind "main" (Just (Ty (substitute subExp exptype))) [] expr], 
                substitute subExp exptype, subExp)
    typeReq -> return ([Bind "main" (Just typeReq) [] expr], substitute subExp exptype, subExp)

inferProgram env bs = error "implement me! don't forget to run the result substitution on the"
                            "entire expression using allTypes from Syntax.hs"

inferExp :: Gamma -> Exp -> TC (Exp, Type, Subst)

-- Num/ constant value type inference.
inferExp gama (Num n) = return (Num n, Base Int, emptySubst)

-- Variable Values type inference.
inferExp gama (Var a) = do 
  
  case E.lookup gama a of 
    
    Just val -> do 
      
      varVal <- unquantify val
      return (Var a, varVal, emptySubst)
    
    Nothing -> typeError $ NoSuchVariable a

-- Con values 

inferExp gama (Con const) = do 
  
  case constType const of 
    
    Just val -> do
      
      conVal <- unquantify val
      return (Con const, conVal, emptySubst)
    
    Nothing -> typeError $ NoSuchConstructor const

-- Primitive operations.

inferExp gama (Prim operation) = do
  
  operator <- unquantify (primOpType operation)
  return (Prim operation, operator, emptySubst)

-- Application of expressions.

inferExp gama (App exp1 exp2) = do
  
  (inferredExp1, typeExp1, substExp1) <- inferExp gama exp1   
  (inferredExp2, typeExp2, substExp2) <- inferExp (substGamma substExp1 gama) exp2
  
  alpha <- fresh
  unifier <- unify (substitute substExp2 typeExp1) (Arrow typeExp2 alpha)
  
  return (App (allTypes (substQType (unifier <> substExp2) ) inferredExp1 ) inferredExp2,
        substitute unifier alpha, unifier <> substExp2 <> substExp1)

-- If conditions

inferExp gama (If cond e1 e2) = do
  
  (inferredCond, condType, substCond) <- inferExp gama cond 
  
  baseUnifier <- unify (condType) (Base Bool)
  let precursor = substGamma (baseUnifier <> substCond) gama
  
  (inferrede1, e1Type, subste1) <- inferExp (precursor) e1
  (inferrede2, e2Type, subste2) <- inferExp (substGamma subste1 precursor) e2
  
  unifier <- unify (substitute subste2 e1Type) e2Type
  let totalSubst = subste2 <> subste1 <> baseUnifier <> substCond
  
  return (If inferredCond inferrede1 inferrede2, substitute unifier e2Type, unifier <> totalSubst)

-- Note: this is the only case you need to handle for case expressions
inferExp gama (Case e [Alt "Inl" [x] e1, Alt "Inr" [y] e2]) = do

  alphaLeft <- fresh
  alphaRight <- fresh 

  let gamLeft = E.add gama (x, Ty alphaLeft) 
  let gamRight = E.add gamLeft (y, Ty alphaRight) 

  (inferredOriginalExp, originalExpType, substOriginalExp) <- inferExp gama e
  (leftExp1, leftExp1Type, substleftExp1) <- inferExp (substGamma substOriginalExp gamLeft) e1
  
  let leftSubst = substGamma (substleftExp1 <> substOriginalExp) gamRight
  (rightExp1, rightExp1Type, substlerightExp1) <- inferExp (leftSubst) e2
  
  let unifyingLeftRight = substlerightExp1 <> substleftExp1 
  let totalUnifying = unifyingLeftRight <> substOriginalExp

  unifierSub <- unify (substitute (totalUnifying) (Sum alphaLeft alphaRight))
            (substitute (unifyingLeftRight) originalExpType)
  unifierUn <- unify (substitute (unifierSub <> substlerightExp1) leftExp1Type)
            (substitute unifierSub rightExp1Type)
  
  let unified = unifierUn <> unifierSub <> substlerightExp1 <> substleftExp1 <> substOriginalExp
  return (Case inferredOriginalExp [Alt "Inl" [x] leftExp1, Alt "Inr" [y] rightExp1],
        substitute (unifierUn <> unifierSub) rightExp1Type, unified)

-- Recursive funtions with only one argument.
inferExp gama (Recfun (Bind funcName ftype [args] progExp)) = do 
  
  alpha1 <- fresh   
  let gfadded = E.add gama (funcName, Ty alpha1)

  alpha2 <- fresh
  let gtypeAdded = E.add gfadded (funcName, Ty alpha1)
  
  (inferredfuncExp, expType, substfuncexp) <- inferExp gtypeAdded progExp
  
  let substAlphatwo = substitute substfuncexp alpha2
  let substAlphaOne = substitute substfuncexp alpha1

  unifier <- unify (substAlphatwo) (Arrow (substAlphaOne) expType)
  
  return (Recfun (Bind funcName (Just (Ty (substitute unifier (Arrow (substAlphaOne) expType)))) 
        [args] inferredfuncExp), substitute unifier (Arrow (substAlphaOne) expType),
        unifier <> substfuncexp)

-- Let bindings considering that only binding is avaiable per let addition.
inferExp gama (Let [(Bind name aType [] argExp)] exp) = do 
  
  (inferredArgExp, argType, substArg) <- inferExp gama argExp
  
  let newGa = substGamma substArg gama
  let genVal = generalise newGa argType
  let gAdded = E.add newGa (name, genVal)
  
  (inferredExp, expType, substExp) <- inferExp gAdded exp
  
  return (Let [Bind name (Just (generalise gAdded argType)) [] inferredArgExp] 
        inferredExp, expType, substExp <> substArg)
