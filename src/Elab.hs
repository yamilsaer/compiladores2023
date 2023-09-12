{-|
Module      : Elab
Description : Elabora un término fully named a uno locally closed.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite elaborar términos y declaraciones para convertirlas desde
fully named (@STerm) a locally closed (@Term@)
-}

module Elab ( elab, typeElab, elabSDecl ) where

import Lang
import Subst
import MonadFD4
import Common

elab :: MonadFD4 m => STerm -> m Term
elab = elab' []

elab' :: MonadFD4 m => [Name] -> STerm -> m Term
elab' env (SV p v) = 
  if v `elem` env 
    then return (V p (Free v))
    else return (V p (Global v))
elab' _ (SConst p c) = return $ Const p c
elab' env (SLam p [] t) = elab' env t
elab' env (SLam p ((v,ty):vs) t) = do
  ty' <- typeElab p ty
  t' <- elab' (v:env) (SLam p vs t)
  return $ Lam p v ty' (close v t')
elab' env (SFix p (f,fty) [] t) = undefined -- No llega nunca
elab' env (SFix p (f,fty) ((x,xty):vs) t) = do
  fty' <- typeElab p fty
  xty' <- typeElab p xty
  t' <- elab' (x:f:env) (SLam p vs t)
  return $ Fix p f fty' x xty' (close2 f x t')
elab' env (SIfZ p c t e) = do
  c' <- elab' env c
  t' <- elab' env t
  e' <- elab' env e
  return $ IfZ p c' t' e'
elab' env (SBinaryOp i o t u) = do
  t' <- elab' env t 
  u' <- elab' env u
  return $ BinaryOp i o t' u'
elab' env (SPrint i str t) = do
  t' <- elab' env t
  return $ Print i str t'
elab' env (SApp p h a) = do
  h' <- elab' env h
  a' <- elab' env a
  return $ App p h' a'
elab' env (SLet b p [] def body) = undefined
elab' env (SLet False p [(v,vty)] def body) = do
  vty' <- typeElab p vty
  def' <- elab' env def
  body' <- elab' (v:env) body
  return $ Let p v vty' def' (close v body')
elab' env (SLet False p ((v,vty):vs) def body) = do
  vty' <- typeElab p vty
  vs' <- mapTypes p vs
  def' <- elab' env (SLam p vs def)
  body' <- elab' (v:env) body
  return $ Let p v (foldr (FunTy . snd) vty' vs') def' (close v body')
elab' env (SLet True p [(f,_)] def body) = failPosFD4 p ("La definicion " ++ f ++ " no tiene suficientes argumentos.")
elab' env (SLet True p [(f,fty),(v,vty)] def body) = do
  fty' <- typeElab p fty
  vty' <- typeElab p vty
  def' <- elab' env (SFix p (f,SFunTy vty fty) [(v,vty)] def)
  body' <- elab' (f:env) body
  return $ Let p f (FunTy vty' fty') def' (close v body')
elab' env (SLet True p ((f,fty):(v,vty):vs) def body) = do
  let fty'' = foldr (SFunTy . snd) fty vs
    in elab' env (SLet True p [(f,fty),(v,vty)] (SLam p vs def) body)

mapTypes :: MonadFD4 m => Pos -> [(Name,STy)] -> m [(Name,Ty)]
mapTypes _ [] = return []
mapTypes p ((n,ty):ts) = do
  ty' <- typeElab p ty
  ts' <- mapTypes p ts
  return $ (n,ty'):ts'

-- elabDecl :: MonadFD4 m => SDecl STerm STy -> m ()
-- elabDecl (SType i n ty) = do
--   nt <- typeElab i ty
--   addTypeDecl (n,nt)
--   return ()
-- elabDecl d@(SDecl i b bs t) =
--   case elabSDecl d of
--     (SDecl i' b' bs' t') -> do t'' <- elab t' ;
--     _ -> return ()

typeElab :: MonadFD4 m => Pos -> STy -> m Ty
typeElab _ SNatTy = return NatTy
typeElab p (SFunTy t1 t2) = do
  t1' <- typeElab p t1 
  t2' <- typeElab p t2
  return (FunTy t1' t2')
typeElab p (SVarTy n) = do
  env <- get
  ty <- lookupTyDecl n 
  case ty of
    Nothing -> failPosFD4 p ("El tipo " ++ n ++ " no existe.")
    Just t -> return t

elabSDecl :: MonadFD4 m => Pos -> Bool -> [(Name,STy)] -> STerm -> m (SDecl STerm STy)
elabSDecl i _ [] _ = failPosFD4 i "Error inesperado."
elabSDecl i False [(f,fty)] t = return (SDecl i False [(f,fty)] t)
elabSDecl i False [(f,fty),(v,vty)] t = return (SDecl i False [(f,SFunTy vty fty)] (SLam i [(v,vty)] t))
elabSDecl i False ((f,fty):vs) t = 
  let fty' = foldr (SFunTy . snd) fty vs
  in return (SDecl i False [(f,fty')] (SLam i vs t))
elabSDecl i True [(f,fty)] t = failPosFD4 i ("La definicion " ++ f ++ " no tiene suficientes argumentos.")
elabSDecl i True [(f,fty),(v,vty)] t = return (SDecl i True [(f,SFunTy vty fty)] (SFix i (f,SFunTy vty fty) [(v,vty)] t))
elabSDecl i True ((f,fty):(v,vty):vs) t =
  let fty' = foldr (SFunTy . snd) fty vs
  in elabSDecl i True [(f,fty'),(v,vty)] t 

-- elabDecl :: SDecl STerm STy -> Decl Term
-- elabDecl = fmap elab

-- | 'elab' transforma variables ligadas en índices de de Bruijn
-- en un término dado. 
-- elab :: STerm -> Term
-- elab = elab' []

-- elab' :: [Name] -> STerm -> Term
-- elab' env (SV p v) =
--   -- Tenemos que ver si la variable es Global o es un nombre local
--   -- En env llevamos la lista de nombres locales.
--   if v `elem` env 
--     then  V p (Free v)
--     else V p (Global v)

-- elab' _ (SConst p c) = Const p c
-- elab' env (SLam p [] t) = elab' env t
-- elab' env (SLam p ((v,ty):vs) t) = Lam p v ty (close v (elab' (v:env) (SLam p vs t)))
-- elab' env (SFix p (f,fty) [] t) = undefined -- No llega nunca
-- elab' env (SFix p (f,fty) ((x,xty):vs) t) = Fix p f fty x xty (close2 f x (elab' (x:f:env) (SLam p vs t)))
-- elab' env (SIfZ p c t e)         = IfZ p (elab' env c) (elab' env t) (elab' env e)
-- -- Operadores binarios
-- elab' env (SBinaryOp i o t u) = BinaryOp i o (elab' env t) (elab' env u)
-- -- Operador Print
-- elab' env (SPrint i str t) = Print i str (elab' env t)
-- -- Aplicaciones generales
-- elab' env (SApp p h a) = App p (elab' env h) (elab' env a)
-- elab' env (SLet b p [] def body) = undefined
-- elab' env (SLet False p [(v,vty)] def body) =
--   Let p v vty (elab' env def) (close v (elab' (v:env) body))
-- elab' env (SLet False p ((v,vty):vs) def body) = 
--   Let p v (foldr (FunTy . snd) vty vs) (elab' env (SLam p vs def)) (close v (elab' (v:env) body))
-- elab' env (SLet True p [(_,_)] def body) = undefined
-- elab' env (SLet True p [(f,fty),(v,vty)] def body) = 
--   Let p f (FunTy vty fty) (elab' env (SFix p (f,FunTy vty fty) [(v,vty)] def)) (close v (elab' (f:env) body))
-- elab' env (SLet True p ((f,fty):(v,vty):vs) def body) =
--   let fty' = foldr (FunTy . snd) fty vs
--   in elab' env (SLet True p [(f,fty'),(v,vty)] (SLam p vs def) body)
-- --where getType = foldr (FunTy . snd)