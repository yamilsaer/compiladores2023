module ClosureConvert where

import IR
import Lang
    ( getTy,
      Decl(declName, declBody),
      Name,
      Scope(Sc1),
      Scope2(Sc2),
      TTerm,
      Tm(Fix, V, Const, App, Print, BinaryOp, IfZ, Let, Lam),
      Ty(..),
      Var(Global, Bound) )
import MonadFD4 ( gets, modify, printFD4, MonadFD4 )
import C (ir2C)
import PPrint (freshen)
import Data.List (find)

createName :: IR Name
createName = do
    n <- gets freshName
    i <- gets freshIndex
    modify (\s -> s {freshIndex = freshIndex s + 1})
    return $ n ++ show i

closureConvert :: TTerm -> IR Ir
closureConvert (V _ (Bound 0)) = do
    irs <- gets lastVar
    return $ head irs
closureConvert v@(V _ (Bound n)) = let ty = ty2irty $ getTy v in do
    x <- gets lastClosure
    return $ IrAccess (IrVar x ty) ty n
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (Const _ n) = return $ IrConst n
closureConvert f@(Lam _ x ty (Sc1 t)) = do
    env <- gets lastVar
    decl <- makeBlock f          
    modify (\s -> s {idecls = idecls s ++ [decl]})
    return $ MkClosure (irDeclName decl) env
closureConvert a@(App i t1 t2) = do 
    t1' <- closureConvert t1 
    t2' <- closureConvert t2 
    return $ IrCall (IrAccess t1' IrFunTy 0) [t1',t2'] (ty2irty $ getTy a)
closureConvert (Print _ str t) = do
    t' <- closureConvert t
    return $ IrPrint str t' 
closureConvert (BinaryOp _ op t1 t2) = do
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrBinaryOp op t1' t2'
closureConvert fx@(Fix _ f fty x xty (Sc2 t)) = do
    env <- gets lastVar
    decl <- makeBlock fx
    modify (\s -> s {idecls = idecls s ++ [decl]})
    return $ MkClosure (irDeclName decl) (IrVar f (ty2irty fty):env)
closureConvert (IfZ _ c t1 t2) = do
    c' <- closureConvert c
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrIfZ c' t1' t2'
closureConvert (Let _ name ty t1 (Sc1 t2)) = do
    t1' <- closureConvert t1
    ity <- irTy t1'
    modify (\s -> s {lastVar = IrVar name (ty2irty ty): lastVar s})
    t2' <- closureConvert t2
    return $ IrLet name ity t1' t2'
closureConvert _= undefined

makeBlock :: TTerm -> IR IrDecl
makeBlock (Lam _ x ty (Sc1 t)) = do
    n' <- createName
    modify (\s -> s {lastClosure = "clo"++ n', lastVar = IrVar x (ty2irty ty): lastVar s})
    ir <- closureConvert t
    ity <- irTy ir
    return $ IrFun n' ity [("clo"++n',IrClo),(x,ty2irty ty)] ir
makeBlock (Fix _ f fty x xty (Sc2 t)) = do
    n' <- createName
    modify (\s -> s {lastClosure = "clo" ++ n', lastVar = IrVar x (ty2irty xty):IrVar f (ty2irty fty): lastVar s})
    ir <- closureConvert t
    ty <- irTy ir
    return $ IrFun n' ty [("clo"++n',IrClo),(x,ty2irty xty)] ir
makeBlock t = do
    n' <- createName
    modify (\s -> s {lastClosure = "clo" ++ n'})
    ir <- closureConvert t
    ty <- irTy ir
    return $ IrVal n' ty ir

ty2irty :: Ty -> IrTy
ty2irty (NatTy _) = IrInt
ty2irty (FunTy {}) = IrClo

irTy :: Ir -> IR IrTy
irTy (IrCall _ _ ty) = return ty
irTy (IrConst _) = return IrInt
irTy (IrPrint _ _) = return IrInt
irTy (IrBinaryOp {}) = return IrInt 
irTy (IrLet _ _ _ i) = irTy i
irTy (IrIfZ _ i _) = irTy i
irTy (MkClosure _ _) = return IrClo
irTy (IrAccess _ ty _) = return ty
irTy (IrGlobal n) = getDeclType n
irTy (IrVar _ ty) = return ty

ir2C2 :: MonadFD4 m => [Decl TTerm] -> m ()
ir2C2 decls = let names = map declName decls
                  name = freshen names "_f" in do
    (a,irs) <- return $ runIR (mapM_ decl2ir decls) name
    --printFD4 $ ir2C $ IrDecls (idecls irs)
    mapM_ (printFD4 . show) (idecls irs)


decl2ir :: Decl TTerm -> IR ()
decl2ir d = do
    modify (\s -> s {lastClosure = declName d})
    ir <- closureConvert (declBody d)
    ty <- irTy ir
    modify (\s -> s {idecls = idecls s ++ [IrVal (declName d) ty ir]}) 

getDeclType :: Name -> IR IrTy
getDeclType n = do
    decls' <- gets idecls
    case find (\d -> irDeclName d == n) decls' of
        Just (IrFun _ ty _ _) -> return ty
        Just (IrVal _ ty _) -> return ty
        Nothing -> return IrInt -- no deberia llegar