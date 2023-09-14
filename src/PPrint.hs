{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Use record patterns" #-}
{-|
Module      : PPrint
Description : Pretty printer para FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module PPrint (
    pp,
    ppTy,
    ppName,
    ppDecl
    ) where

import Lang
import Subst ( open, open2 )
import Common ( Pos )

import Data.Text ( unpack )
import Data.List ( groupBy )
import Prettyprinter.Render.Terminal
  ( renderStrict, italicized, color, colorDull, Color (..), AnsiStyle )
import Prettyprinter
    ( (<+>),
      annotate,
      defaultLayoutOptions,
      layoutSmart,
      nest,
      sep,
      parens,
      emptyDoc,
      cat,
      Doc,
      Pretty(pretty) )
import MonadFD4 ( gets, MonadFD4 )
import Global ( GlEnv(glb) )

freshen :: [Name] -> Name -> Name
freshen ns n = let cands = n : map (\i -> n ++ show i) [0..] 
               in head (filter (`notElem` ns) cands)

-- | 'openAll' convierte términos locally nameless
-- a términos fully named abriendo todos las variables de ligadura que va encontrando
-- Debe tener cuidado de no abrir términos con nombres que ya fueron abiertos.
-- Estos nombres se encuentran en la lista ns (primer argumento).
openAll :: (i -> Pos) -> [Name] -> Tm i Var -> STerm
openAll gp ns (V p v) = case v of 
      Bound i ->  SV (gp p) $ "(Bound "++show i++")" --este caso no debería aparecer
                                               --si el término es localmente cerrado
      Free x -> SV (gp p) x
      Global x -> SV (gp p) x
openAll gp ns (Const p c) = SConst (gp p) c
openAll gp ns (Lam p x ty t) = 
  let x' = freshen ns x 
      ty' = typeToSType ty
  in SLam (gp p) [(x',ty')] (openAll gp (x':ns) (open x' t))
openAll gp ns (App p t u) = SApp (gp p) (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Fix p f fty x xty t) = 
  let 
    x' = freshen ns x
    f' = freshen (x':ns) f
    fty' = typeToSType fty
    xty' = typeToSType xty
  in SFix (gp p) (f',fty') [(x',xty')] (openAll gp (x:f:ns) (open2 f' x' t))                   
openAll gp ns (IfZ p c t e) = SIfZ (gp p) (openAll gp ns c) (openAll gp ns t) (openAll gp ns e)
openAll gp ns (Print p str t) = SPrint (gp p) str (Just (openAll gp ns t))
openAll gp ns (BinaryOp p op t u) = SBinaryOp (gp p) op (openAll gp ns t) (openAll gp ns u)
openAll gp ns (Let p v ty m n) = 
    let v' = freshen ns v
        ty' = typeToSType ty
    in  SLet False (gp p) [(v',ty')] (openAll gp ns m) (openAll gp (v':ns) (open v' n))       

typeToSType :: Ty -> STy
typeToSType (NatTy Nothing) = SNatTy
typeToSType (NatTy (Just n)) = SVarTy n
typeToSType (FunTy Nothing t1 t2) = SFunTy (typeToSType t1) (typeToSType t2)
typeToSType (FunTy (Just n) t1 t2) = SVarTy n

--Colores
constColor :: Doc AnsiStyle -> Doc AnsiStyle
constColor = annotate (color Red)
opColor :: Doc AnsiStyle -> Doc AnsiStyle
opColor = annotate (colorDull Green)
keywordColor :: Doc AnsiStyle -> Doc AnsiStyle
keywordColor = annotate (colorDull Green) -- <> bold
typeColor :: Doc AnsiStyle -> Doc AnsiStyle
typeColor = annotate (color Blue <> italicized)
typeOpColor :: Doc AnsiStyle -> Doc AnsiStyle
typeOpColor = annotate (colorDull Blue)
defColor :: Doc AnsiStyle -> Doc AnsiStyle
defColor = annotate (colorDull Magenta <> italicized)
nameColor :: Doc AnsiStyle -> Doc AnsiStyle
nameColor = id

-- | Pretty printer de nombres (Doc)
name2doc :: Name -> Doc AnsiStyle
name2doc n = nameColor (pretty n)

-- |  Pretty printer de nombres (String)
ppName :: Name -> String
ppName = id

-- | Pretty printer para tipos (Doc)
ty2doc :: Ty -> Doc AnsiStyle
ty2doc (NatTy Nothing) = typeColor (pretty "Nat")
ty2doc (NatTy (Just n)) = name2doc n
ty2doc (FunTy (Just n) x y) = name2doc n
ty2doc (FunTy Nothing x@(FunTy Nothing _ _) y) = sep [parens (ty2doc x), typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy Nothing x@(FunTy (Just _) _ _) y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y]
ty2doc (FunTy Nothing x y) = sep [ty2doc x, typeOpColor (pretty "->"),ty2doc y] 

sty2doc :: STy -> Doc AnsiStyle
sty2doc SNatTy     = typeColor (pretty "Nat")
sty2doc (SFunTy x@(SFunTy _ _) y) = sep [parens (sty2doc x), typeOpColor (pretty "->"),sty2doc y]
sty2doc (SFunTy x y) = sep [sty2doc x, typeOpColor (pretty "->"),sty2doc y]
sty2doc (SVarTy n) = name2doc n 

-- | Pretty printer para tipos (String)
ppTy :: Ty -> String
ppTy = render . ty2doc

c2doc :: Const -> Doc AnsiStyle
c2doc (CNat n) = constColor (pretty (show n))

binary2doc :: BinaryOp -> Doc AnsiStyle
binary2doc Add = opColor (pretty "+")
binary2doc Sub = opColor (pretty "-")

collectApp :: STerm -> (STerm, [STerm])
collectApp = go [] where
  go ts (SApp _ h tt) = go (tt:ts) h
  go ts h = (h, ts)

parenIf :: Bool -> Doc a -> Doc a
parenIf True = parens
parenIf _ = id

-- t2doc at t :: Doc
-- at: debe ser un átomo
-- | Pretty printing de términos (Doc)
t2doc :: Bool     -- Debe ser un átomo? 
      -> STerm    -- término a mostrar
      -> Doc AnsiStyle
-- Uncomment to use the Show instance for STerm
{- t2doc at x = text (show x) -}
t2doc at (SV _ x) = name2doc x
t2doc at (SConst _ c) = c2doc c

t2doc at (SLam _ vs t) =
  parenIf at $
  sep [sep [ keywordColor (pretty "fun")
           , args2doc vs
           , opColor(pretty "->")]
      , nest 2 (t2doc False t)]

t2doc at t@(SApp _ _ _) =
  let (h, ts) = collectApp t in
  parenIf at $
  t2doc True h <+> sep (map (t2doc True) ts)

t2doc at (SFix _ (f,fty) vs m) =
  parenIf at $
  sep [ sep [keywordColor (pretty "fix")
                  , binding2doc (f, fty)
                  , args2doc vs
                  , opColor (pretty "->") ]
      , nest 2 (t2doc False m)
      ]
t2doc at (SIfZ _ c t e) =
  parenIf at $
  sep [keywordColor (pretty "ifz"), nest 2 (t2doc False c)
     , keywordColor (pretty "then"), nest 2 (t2doc False t)
     , keywordColor (pretty "else"), nest 2 (t2doc False e) ]

t2doc at (SPrint _ str t) =
  case t of
    Just t' ->
      parenIf at $
      sep [keywordColor (pretty "print"), pretty (show str), t2doc True t']
    Nothing ->
      parenIf at $
      sep [keywordColor (pretty "print"), pretty (show str)]
      
t2doc at (SLet isRec _ vs t t') =
  parenIf at $
  sep [
    sep [keywordColor (pretty "let")
       , if isRec then keywordColor (pretty "rec") else emptyDoc
       , name2doc (fst $ head vs)
       , args2doc (tail vs)
       , pretty ":"
       , sty2doc (snd $ head vs)
       , opColor (pretty "=") ]
  , nest 2 (t2doc False t)
  , keywordColor (pretty "in")
  , nest 2 (t2doc False t') ]

t2doc at (SBinaryOp _ o a b) =
  parenIf at $
  t2doc True a <+> binary2doc o <+> t2doc True b

binding2doc :: (Name, STy) -> Doc AnsiStyle
binding2doc (x, ty) =
  parens (sep [name2doc x, pretty ":", sty2doc ty])

args2doc :: [(Name,STy)] -> Doc AnsiStyle
args2doc vs =
  let vs' = groupBy (\x y -> snd x == snd y) vs
  in cat $ map argsAux vs'
  where argsAux xs = parens $ sep [
          sep $ map (name2doc.fst) xs
          , pretty ":"
          , sty2doc (snd $ head xs)]

-- | Pretty printing de términos (String)
pp :: MonadFD4 m => TTerm -> m String
-- Uncomment to use the Show instance for Term
{- pp = show -}
pp t = do
       gdecl <- gets glb
       t' <- resugarT t
       return (render . t2doc False $ t')

render :: Doc AnsiStyle -> String
render = unpack . renderStrict . layoutSmart defaultLayoutOptions

sDecl2doc :: SDecl STerm b -> Doc AnsiStyle
sDecl2doc (SDecl p isRec vs t) =
  sep [
    sep [keywordColor (pretty "let")
       , if isRec then keywordColor (pretty "rec") else emptyDoc
       , name2doc (fst $ head vs)
       , args2doc (tail vs)
       , pretty ":"
       , sty2doc (snd $ head vs)
       , opColor (pretty "=") ]
    , nest 2 (t2doc False t)]
sDecl2doc _ = emptyDoc

-- | Pretty printing de declaraciones
ppDecl :: MonadFD4 m => Decl TTerm -> m String
ppDecl dc@(Decl p x xty t) = do 
  gdecl <- gets glb
  sd <- resugarD dc
  return (render $ sDecl2doc sd)


resugarT :: MonadFD4 m => TTerm -> m STerm
resugarT t = do
  gdecl <- gets glb
  return (resugar' $ openAll fst (map declName gdecl) t)

lastTy :: STy -> STy
lastTy (SFunTy t1 t2) = lastTy t2
lastTy t = t

resugar' :: STerm -> STerm
resugar' (SV p v) = SV p v
resugar' (SConst p c) = SConst p c
resugar' (SIfZ p c t e ) = SIfZ p (resugar' c) (resugar' t) (resugar' e)
resugar' (SBinaryOp i o t u) = SBinaryOp i o (resugar' t) (resugar' u)
resugar' (SApp p h a) = SApp p (resugar' h) (resugar' a)
resugar' (SPrint i str m) = SPrint i str m
resugar' st@(SLam i [(x,ty)] (SPrint _ str (Just (SV _ y)))) = if x == y then SPrint i str Nothing else st
resugar' (SLam i vs (SLam _ vs2 t)) = resugar' (SLam i (vs ++ vs2) t)
resugar' (SLam i vs t) = SLam i vs (resugar' t)
resugar' (SFix p (f,fty) vs (SLam p2 vs2 t)) = resugar' (SFix p (f,fty) (vs ++ vs2) t)
resugar' (SFix p (f,fty) vs t) = SFix p (f,fty) vs (resugar' t)
resugar' (SLet b p [(x,xty)] (SLam _ vs t) body) = resugar' (SLet b p ((x,lastTy xty):vs) t body)
resugar' (SLet False p [(x,xty)] (SFix _ (f,fty) vs t) body) = resugar' (SLet True p ((f,lastTy fty):vs) t body) 
resugar' (SLet True p [(f,fty),(x,xty)] (SLam _ vs2 t) body) = resugar' (SLet True p ((f,lastTy fty):(x,xty):vs2) t body)
resugar' (SLet b p vs def body) = SLet b p vs (resugar' def) (resugar' body)

resugarD :: MonadFD4 m => Decl TTerm -> m (SDecl STerm STy)
resugarD (Decl p n ty t) = do
  gdecl <- gets glb 
  t' <- resugarT t
  return $ resugarD' $ SDecl p False [(n,typeToSType ty)] t'
  
resugarD' :: SDecl STerm STy -> SDecl STerm STy
resugarD' (SDecl p b [(n,ty)] (SLam _ vs t)) = SDecl p b ((n,lastTy ty):vs) t
resugarD' sd@(SDecl p False [(f,fty)] (SFix _ (f',fty') vs t)) = if f == f' && fty == fty'
  then resugarD' $ SDecl p True ((f,lastTy fty):vs) t
  else sd
resugarD' (SDecl p True [(f,fty),(x,xty)] (SLam _ vs t)) = 
  resugarD' $ SDecl p True ((f,lastTy fty):(x,xty):vs) t
resugarD' t = t
