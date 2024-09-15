module ClosureConvert where

import IR
import Lang
import MonadFD4 ( gets, modify, MonadFD4 )
import C (ir2C)
import PPrint (freshen)
import Data.List (find)
import Subst (open,open2)

createName :: IR Name
createName = do
    n <- gets freshName
    i <- gets freshIndex
    modify (\s -> s {freshIndex = freshIndex s + 1})
    return $ n ++ show i

closureConvert :: TTerm -> IR Ir
closureConvert v@(V _ (Free n)) = return $ IrVar n (ty2irty $ getTy v)
closureConvert (V _ (Global n)) = return $ IrGlobal n
closureConvert (Const _ n) = return $ IrConst n
closureConvert f@(Lam _ x ty sc@(Sc1 t)) = do
    n' <- createName
    n'' <- createName
    y <- createName
    let fv = freeVars t
    let irfv = map (IrGlobal . fst) fv
    ir <- closureConvert (open y sc)
    let decl = IrFun n' ((ty2irty . getTy) t) [(n'',IrClo),(y,ty2irty ty)] (putLet ir fv n'' 1)
    modify (\s -> s {idecls = idecls s ++ [decl]})
    return $ MkClosure n' irfv
closureConvert a@(App i t1 t2) = do
    let FunTy _ ty1 ty2 = getTy t1 
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    n <- createName
    let v = IrVar n IrClo
    return $ IrLet n IrClo t1' (IrCall (IrAccess v IrFunTy 0) [v,t2'] (ty2irty $ getTy a))
closureConvert (Print _ str t) = do
    n <- createName
    t' <- closureConvert t
    let ty = ty2irty $ getTy t
    return $ IrLet n ty t' (IrPrint str (IrVar n ty))
closureConvert (BinaryOp _ op t1 t2) = do
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrBinaryOp op t1' t2'
closureConvert fx@(Fix _ f fty x xty sc@(Sc2 t)) = do
    n' <- createName
    n'' <- createName
    f2 <- createName
    x2 <- createName
    let fv = freeVars t
    let irfv = map (IrGlobal . fst) fv
    ir <- closureConvert (open2 f2 x2 sc)
    let body = putLet ir fv n'' 1
    let decl =  IrFun n' (ty2irty $ getTy t) [(n'',IrClo),(x2,ty2irty xty)] (IrLet f2 (ty2irty $ getTy fx) (IrVar n'' IrClo) body) 
    modify (\s -> s {idecls = idecls s ++ [decl]})
    return $ MkClosure n' irfv
closureConvert (IfZ _ c t1 t2) = do
    c' <- closureConvert c
    t1' <- closureConvert t1
    t2' <- closureConvert t2
    return $ IrIfZ c' t1' t2'
closureConvert (Let _ name ty t1 t2) = do
    x <- createName
    t1' <- closureConvert t1
    t2' <- closureConvert (open x t2)
    return $ IrLet x (ty2irty ty) t1' t2'
closureConvert v@(V _ (Bound n)) = return $ IrVar "" IrInt -- no deberia llegar

putLet :: Ir -> [(Name,Ty)] -> Name -> Int -> Ir
putLet t [] _ _ = t
putLet t ((v,ty):vs) n i = IrLet v (ty2irty ty) (IrAccess (IrVar n IrClo) (ty2irty ty) i) (putLet t vs n (i+1))

ty2irty :: Ty -> IrTy
ty2irty (NatTy {}) = IrInt
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

ir2C2 :: MonadFD4 m => [Decl TTerm] -> m String
ir2C2 decls = let names = map declName decls ++ concatMap (getNames . declBody) decls
                  name = freshen names "_f" in do
    (a,irs) <- return $ runIR (mapM_ decl2ir decls) name
    return $ ir2C $ IrDecls (idecls irs)

getNames :: TTerm -> [Name]
getNames (V _ (Global _)) = []
getNames (V _ (Bound _)) = []
getNames (V _ (Free n)) = [n] -- no deberia llegar
getNames (Const {}) = []
getNames (Lam _ x _ (Sc1 t)) = x:getNames t
getNames (App _ t1 t2) = getNames t1 ++ getNames t2
getNames (Print _ _ t) = getNames t
getNames (BinaryOp _ _ t1 t2) = getNames t1 ++ getNames t2
getNames (IfZ _ c t1 t2) = getNames c ++ getNames t1 ++ getNames t2 
getNames (Fix _ f _ x _ (Sc2 t)) = f:x:getNames t
getNames (Let _ x _ t1 (Sc1 t2)) = x:(getNames t1 ++ getNames t2)  

decl2ir :: Decl TTerm -> IR ()
decl2ir d = do
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