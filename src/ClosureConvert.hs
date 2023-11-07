module ClosureConvert where

import IR
import Lang
import Control.Monad.Writer.Lazy (tell)
import MonadFD4
import C (ir2C)

createName :: Int -> Name
createName n = "_f" ++ show n


closureConvert :: TTerm -> [Ir] -> Name -> IR Ir
closureConvert (V _ (Bound 0)) ns _ = return $ head ns
closureConvert v@(V i (Bound n)) ns x = return $ IrAccess (IrVar x) (ty2irty $ getTy v) (n-1)
closureConvert (V _ (Global n)) _  _ = return $ IrGlobal n
closureConvert (Const _ n) ns _ = return $ IrConst n
closureConvert f@(Lam _ x ty (Sc1 t)) ns _ = do
    decl <- makeBlock f ns          
    tell [decl]
    return $ MkClosure (irDeclName decl) ns
closureConvert (App _ t1 t2) ns x = do 
    t1' <- closureConvert t1 ns x
    t2' <- closureConvert t2 ns x
    return $ IrCall (IrAccess t1' IrFunTy 0) (t1':t2':ns) IrFunTy
closureConvert (Print _ str t) ns x = do
    t' <- closureConvert t ns x
    return $ IrPrint str t' 
closureConvert (BinaryOp _ op t1 t2) ns x = do
    t1' <- closureConvert t1 ns x
    t2' <- closureConvert t2 ns x
    return $ IrBinaryOp op t1' t2'
closureConvert fx@(Fix _ f fty x xty (Sc2 t)) ns _ = do
    decl <- makeBlock fx ns
    tell [decl]
    return $ MkClosure (irDeclName decl) ns
closureConvert (IfZ _ c t1 t2) ns x = do
    c' <- closureConvert c ns x
    t1' <- closureConvert t1 ns x
    t2' <- closureConvert t2 ns x
    return $ IrIfZ c' t1' t2'
closureConvert (Let _ name ty t1 (Sc1 t2)) ns x = do
    t1' <- closureConvert t1 ns x
    t2' <- closureConvert t2 (IrVar name:ns) x
    return $ IrLet name (irTy t1') t1' t2'
closureConvert _ _ _= undefined

makeBlock :: TTerm -> [Ir] -> IR IrDecl
makeBlock (Lam _ x ty (Sc1 t)) ns = do
    n <- get
    put (n+1)
    let n' = createName n in do
        ir <- closureConvert t (IrVar x:ns) (n'++"clo")
        return $ IrFun n' (irTy ir) [(n'++"clo",IrClo),(x,ty2irty ty)] ir
makeBlock (Fix _ f fty x xty (Sc2 t)) ns = do
    n <- get
    put (n+1)
    let n' = createName n in do
        ir <- closureConvert t (IrVar x:IrVar f:ns) (n'++"clo")
        return $ IrFun n' (irTy ir) [(n'++"clo",IrClo),(f,ty2irty fty),(x,ty2irty xty)] ir
makeBlock t ns = do
    n <- get
    put (n+1)
    let n' = createName n in do
        ir <- closureConvert t ns n'
        return $ IrVal n' (irTy ir) ir

ty2irty :: Ty -> IrTy
ty2irty (NatTy _) = IrInt
ty2irty (FunTy {}) = IrFunTy

irTy :: Ir -> IrTy
irTy (IrCall _ _ ty) = ty
irTy (IrConst _) = IrInt
irTy (IrPrint _ _) = IrInt
irTy (IrBinaryOp {}) = IrInt 
irTy (IrLet _ ty _ _) = ty
irTy (IrIfZ _ i _) = irTy i
irTy (MkClosure _ _) = IrClo
irTy (IrAccess _ ty _) = ty
irTy (IrGlobal _) = IrInt
irTy (IrVar _) = IrInt

ir2C2 :: MonadFD4 m => [Decl TTerm] -> m ()
ir2C2 decls = do
    (a,irs) <- return $ runIR (mapM_ decl2ir decls)
    --printFD4 $ ir2C $ IrDecls irs
    mapM_ (printFD4 . show) irs


decl2ir :: Decl TTerm -> IR ()
decl2ir d = do
    ir <- closureConvert (declBody d) [] (declName d)
    tell [IrVal (declName d) (irTy ir) ir]