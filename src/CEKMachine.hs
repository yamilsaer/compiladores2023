module CEKMachine where
import Lang
import MonadFD4
import Eval(semOp)
import PPrint(ppName)
import Common

type Env = [Value]

data Value = Vm Int 
    | C Clos

data Clos = CFun Env Name Ty TTerm 
    | CFix Env Name Ty Name Ty TTerm -- CFix Env f x t

data Frame = KArg Env TTerm
    | KClos Clos
    | KIf Env TTerm TTerm
    | KOp Env BinaryOp TTerm
    | KOpVal Int BinaryOp
    | KPrint String
    | KLet Env Name TTerm

type Kont = [Frame]

destroy :: MonadFD4 m => Value -> Kont -> m Value
destroy v [] = return v
destroy (Vm n) ((KPrint str):ks) = do
    printFD4 (str++show n)
    destroy (Vm n) ks
destroy (Vm n) ((KOp e op u):ks) = seek u e (KOpVal n op:ks)
destroy (Vm n') ((KOpVal n op):ks) = destroy (Vm (semOp op n n')) ks
destroy (Vm 0) (KIf e t u:ks) = seek t e ks
destroy (Vm n) (KIf e t u:ks) = seek u e ks
destroy (C c) (KArg e t:ks) = seek t e (KClos c:ks)
destroy v (KClos (CFun e n _ t):ks) = seek t (v:e) ks
destroy v (KClos c@(CFix e f _ n _ t):ks) = seek t (v:C c:e) ks
destroy v (KLet e n t:ks) = seek t (v:e) ks
destroy _ _ = undefined

seek :: MonadFD4 m => TTerm -> Env -> Kont -> m Value
seek (Print _ str t) e ks =  seek t e (KPrint str:ks)
seek (BinaryOp _ op t u) e ks =  seek t e (KOp e op u:ks)
seek (IfZ _ c t u) e ks =  seek c e (KIf e t u:ks)
seek (App _ t u) e ks =  seek t e (KArg e u:ks)
seek (V _ (Bound i)) e ks =  destroy (e !! i) ks
seek (V _ (Global n)) e ks = do
    mtm <- lookupDecl n
    case mtm of
        Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n
        Just t -> seek t e ks
seek (V _ (Free n)) e ks = undefined
seek (Const _ (CNat n)) _ ks = destroy (Vm n) ks
seek (Lam _ n ty (Sc1 t)) e ks = destroy (C (CFun e n ty t)) ks
seek (Fix _ f fty n ty (Sc2 t)) e ks = destroy (C (CFix e f fty n ty t)) ks
seek (Let _ n _ t1 (Sc1 t2)) e ks = seek t1 e (KLet e n t2:ks)


valueToTerm :: MonadFD4 m => Value -> m TTerm
valueToTerm (Vm n) = return (Const (NoPos,NatTy Nothing) (CNat n))
valueToTerm (C (CFun _ n ty t)) = return (Lam (NoPos,ty) n ty (Sc1 t))
valueToTerm (C (CFix _ f fty n ty t)) = return (Fix (NoPos,ty) f fty n ty (Sc2 t))

evalCEK :: MonadFD4 m => TTerm -> m TTerm
evalCEK t = do
      v <- seek t [] []
      valueToTerm v