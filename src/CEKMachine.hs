module CEKMachine where
import Lang
import MonadFD4
import Eval(semOp)
import PPrint(ppName)
import Common
import Global
type Env = [Value]

data Value = Vm Int 
    | C Clos

data Clos = CFun Ty Env Name Ty TTerm 
    | CFix Ty Env Name Ty Name Ty TTerm -- CFix Env f x t

data Frame = KArg Env TTerm
    | KClos Clos
    | KIf Env TTerm TTerm
    | KOp Env BinaryOp TTerm
    | KOpVal Int BinaryOp
    | KPrint String
    | KLet Env Name TTerm

type Kont = [Frame]

destroy :: MonadFD4 m => Value -> Kont -> m Value
destroy v [] = tick >> return v
destroy (Vm n) ((KPrint str):ks) = do
    printFD4 (str++show n)
    tick >> destroy (Vm n) ks
destroy (Vm n) ((KOp e op u):ks) = tick >> seek u e (KOpVal n op:ks)
destroy (Vm n') ((KOpVal n op):ks) = tick >> destroy (Vm (semOp op n n')) ks
destroy (Vm 0) (KIf e t u:ks) = tick >> seek t e ks
destroy (Vm n) (KIf e t u:ks) = tick >> seek u e ks
destroy (C c) (KArg e t:ks) = tick >> seek t e (KClos c:ks)
destroy v (KClos (CFun _ e n _ t):ks) = tick >> seek t (v:e) ks
destroy v (KClos c@(CFix _ e f _ n _ t):ks) = tick >> seek t (v:C c:e) ks
destroy v (KLet e n t:ks) = tick >> seek t (v:e) ks
destroy _ _ = undefined

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Value
seek (Print _ str t) e ks = tick >>  seek t e (KPrint str:ks)
seek (BinaryOp _ op t u) e ks = tick >> seek t e (KOp e op u:ks)
seek (IfZ _ c t u) e ks = tick >> seek c e (KIf e t u:ks)
seek (App _ t u) e ks = tick >> seek t e (KArg e u:ks)
seek (V _ (Bound i)) e ks =  tick >> destroy (e !! i) ks
seek (V _ (Global n)) e ks = do
    mtm <- lookupDecl n
    case mtm of
        Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n
        Just t -> tick >> seek t e ks
seek (V _ (Free n)) e ks = undefined
seek (Const _ (CNat n)) _ ks = tick >> destroy (Vm n) ks
seek (Lam i n ty (Sc1 t)) e ks = tick >> destroy (C (CFun (snd i) e n ty t)) ks
seek (Fix i f fty n ty (Sc2 t)) e ks = tick >> destroy (C (CFix (snd i) e f fty n ty t)) ks
seek (Let _ n _ t1 (Sc1 t2)) e ks = tick >> seek t1 e (KLet e n t2:ks)

-- Reemplazo de la sustitución, razón de creación desconocida
replaceBound :: MonadFD4 m => TTerm -> TTerm -> Int -> m TTerm
replaceBound v@(V _ (Bound j)) t n = return $ if j == n then t else v
replaceBound v@(V _ _) _ _ = return v
replaceBound c@(Const _ _) _ _ = return c
replaceBound (Lam i x ty (Sc1 t)) t' n = do
    t'' <- replaceBound t t' (n+1)
    return $ Lam i x ty (Sc1 t'')
replaceBound (App i t1 t2) t n = do
    t1' <- replaceBound t1 t n
    t2' <- replaceBound t2 t n
    return $ App i t1' t2'
replaceBound (Print i str t) t' n = do
    t'' <- replaceBound t t' n
    return $ Print i str t''
replaceBound (BinaryOp i op t1 t2) t n = do
    t1' <- replaceBound t1 t n
    t2' <- replaceBound t2 t n
    return $ BinaryOp i op t1' t2'
replaceBound (IfZ i c t1 t2) t n = do
    c' <- replaceBound c t n
    t1' <- replaceBound t1 t n
    t2' <- replaceBound t2 t n
    return $ IfZ i c' t1' t2'
replaceBound (Fix i f fty x ty (Sc2 t)) t' n = do
    t'' <- replaceBound t t' (n+2)
    return $ Fix i f fty x ty (Sc2 t'')
replaceBound (Let i x ty t1 (Sc1 t2)) t n = do
    t1' <- replaceBound t1 t n
    t2' <- replaceBound t2 t (n+1)
    return $ Let i x ty t1' (Sc1 t2')

valueToTerm :: MonadFD4 m => Value -> Int -> m TTerm
valueToTerm (Vm n) _ = return (Const (NoPos,NatTy Nothing) (CNat n))
valueToTerm (C (CFun fty [] n ty t)) _ = return (Lam (NoPos,fty) n ty (Sc1 t))
valueToTerm (C (CFun fty (v:vs) n ty t)) d = do
    t' <- valueToTerm (C (CFun fty vs n ty t)) (d+1)
    v' <- valueToTerm v 0
    replaceBound t' v' d
valueToTerm (C (CFix fty' [] f fty n ty t)) _ = return (Fix (NoPos,fty') f fty n ty (Sc2 t))
valueToTerm (C (CFix fty' (v:vs) f fty n ty t)) d = do
    t' <- valueToTerm (C (CFix fty' vs f fty n ty t)) (d+1)
    v' <- valueToTerm v 0
    replaceBound t' v' d

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
    v <- seek t [] []
    p <- getProfile
    when p $ do
      c <- gets count
      printFD4 $ "Cantidad de operaciones ejecutadas : " ++ show c
      resetCount
    valueToTerm v 0