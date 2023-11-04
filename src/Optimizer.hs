{-# LANGUAGE PatternSynonyms #-}

module Optimizer (optimize)
where

import Lang
    ( Scope2(Sc2),
      Scope(Sc1),
      Var(Bound, Global),
      TTerm,
      Tm(Let, V, Const, BinaryOp, Print, Lam, App, IfZ, Fix),
      BinaryOp(Add, Sub),
      Const(CNat),
      Name,
      getInfo )
import MonadFD4 (MonadFD4,lookupDecl, failFD4)
import Subst (subst)
import PPrint (ppName,freshen)

pattern COST :: Int
pattern COST     = 10

optimize :: MonadFD4 m => TTerm -> m TTerm
optimize t = iterate (>>= optimizer) (return t) !! 3


optimizer :: MonadFD4 m => TTerm -> m TTerm
optimizer t = do
    t1 <- consPropagation t
    t2 <- consFolding t1
    t3 <- inline t2 [] []
    deadCode t3
    
consFolding :: MonadFD4 m => TTerm -> m TTerm
consFolding v@(V _ _) = return v
consFolding c@(Const _ _) = return c
consFolding (Lam i n ty (Sc1 t)) = do
    t' <- consFolding t
    return $ Lam i n ty (Sc1 t')
consFolding (App i t1 t2) = do
    t1' <- consFolding t1
    t2' <- consFolding t2
    return $ App i t1' t2'
consFolding (Print i st t) = do
    t' <- consFolding t
    return $ Print i st t'
consFolding (Fix i f fty x xty (Sc2 t)) = do
    t' <- consFolding t
    return $ Fix i f fty x xty (Sc2 t')
consFolding (IfZ i c t0 t1) = do
    c' <- consFolding c
    case c' of
        Const _ (CNat 0) -> consFolding t0
        Const _ (CNat _) -> consFolding t1
        t -> do
            t0' <- consFolding t0
            t1' <- consFolding t1
            return $ IfZ i c' t0' t1'
consFolding (Let i x xty def (Sc1 body)) = do
    def' <- consFolding def
    body' <- consFolding body
    return $ Let i x xty def' (Sc1 body')
consFolding (BinaryOp i Sub t1 t2) = do 
    t1' <- consFolding t1
    t2' <- consFolding t2
    case t1' of
        Const i2 (CNat 0) -> if hasPrint t2' 
            then return $ BinaryOp i Sub t1' t2'
            else return $ Const i2 (CNat 0)
        Const _ (CNat n1) -> case t2' of
            Const _ (CNat n2) -> return $ Const i (CNat $ max 0 (n1-n2))
            _ -> return $ BinaryOp i Sub t1' t2'
        _ -> case t2' of 
            Const _ (CNat 0) -> return t1'
            _ -> return $ BinaryOp i Sub t1' t2'
consFolding (BinaryOp i Add t1 t2) = do 
    t1' <- consFolding t1
    t2' <- consFolding t2
    case t1' of
        Const _ (CNat 0) -> return t2'
        Const _ (CNat n1) -> case t2' of
            Const _ (CNat n2) -> return $ Const i (CNat $ n1+n2)
            _ -> return $ BinaryOp i Add t1' t2'
        _ -> case t2' of 
            Const _ (CNat 0) -> return t1'
            _ -> return $ BinaryOp i Add t1' t2'

consPropagation :: MonadFD4 m => TTerm -> m TTerm
consPropagation v@(V _ _) = return v
consPropagation c@(Const _ _) = return c
consPropagation (Lam i n ty (Sc1 t)) = do
    t' <- consPropagation t
    return $ Lam i n ty (Sc1 t')
consPropagation (App i t1 t2) = do
    t1' <- consPropagation t1
    t2' <- consPropagation t2
    return $ App i t1' t2'
consPropagation (Print i st t) = do
    t' <- consPropagation t
    return $ Print i st t'
consPropagation (Fix i f fty x xty (Sc2 t)) = do
    t' <- consPropagation t
    return $ Fix i f fty x xty (Sc2 t')
consPropagation (IfZ i c t0 t1) = do
    c' <- consPropagation c
    t0' <- consPropagation t0
    t1' <- consPropagation t1
    return $ IfZ i c' t0' t1' 
consPropagation (Let i x xty def (Sc1 body)) = do
    def' <- consPropagation def
    case def' of
        Const i2 c -> let body' = subst (Const i2 c) (Sc1 body) in 
            do
            body'' <- consPropagation body'
            return $ Let i x xty def' (Sc1 body')
        t -> do
            body' <- consPropagation body
            return $ Let i x xty def' (Sc1 body')
consPropagation (BinaryOp i op t1 t2) = do 
    t1' <- consPropagation t1
    t2' <- consPropagation t2
    return $ BinaryOp i op t1' t2'

deadCode :: MonadFD4 m =>  TTerm -> m TTerm
deadCode v@(V _ _) = return v
deadCode c@(Const _ _) = return c
deadCode (Lam i n ty (Sc1 t)) = do
    t' <- deadCode t 
    return $ Lam i n ty (Sc1 t')
deadCode (App i t1 t2) = do
    t1' <- deadCode t1
    t2' <- deadCode t2
    return $ App i t1' t2'
deadCode (Print i st t) = do
    t' <- deadCode t
    return $ Print i st t'
deadCode (Fix i f fty x xty (Sc2 t)) = do
    t' <- deadCode t
    return $ Fix i f fty x xty (Sc2 t')
deadCode (IfZ i c t0 t1) = do
    c' <- deadCode c
    t0' <- deadCode t0
    t1' <- deadCode t1
    return $ IfZ i c' t0' t1' 
deadCode (Let i x xty def (Sc1 body)) = do
    if not (hasPrint def) && not (occurs body 0) then
        deadCode $ mapBound body 0
    else do
        def' <- deadCode def
        body' <- deadCode body
        return $ Let i x xty def' (Sc1 body')
deadCode (BinaryOp i op t1 t2) = do 
    t1' <- deadCode t1
    t2' <- deadCode t2
    return $ BinaryOp i op t1' t2'

hasPrint :: TTerm -> Bool
hasPrint (V _ _) = False
hasPrint (Const _ _) = False
hasPrint (Lam _ _ _ (Sc1 t)) = hasPrint t
hasPrint (App _ t1 t2) = hasPrint t1  || hasPrint t2
hasPrint Print {} = True
hasPrint (BinaryOp _ _ t1 t2) = hasPrint t1  || hasPrint t2
hasPrint (Fix _ _ _ _ _ (Sc2 t)) = hasPrint t
hasPrint (IfZ _ c t1 t2) = hasPrint c || hasPrint t1 || hasPrint t2
hasPrint (Let _ _ _  t1 (Sc1 t2)) = hasPrint t1 || hasPrint t2

occurs :: TTerm -> Int -> Bool
occurs (V _ (Bound n1)) n2 = n1 == n2
occurs (V _ _ ) _ = False
occurs (Const _ _) _ = False
occurs (Lam _ _ _ (Sc1 t)) n = occurs t (n+1) 
occurs (App _ t1 t2) n = occurs t1 n || occurs t2 n
occurs (Print _ _ t) n = occurs t n
occurs (BinaryOp _ _ t1 t2) n = occurs t1 n || occurs t2 n
occurs (Fix _ _ _ _ _ (Sc2 t)) n = occurs t (n+2)
occurs (IfZ _ c t1 t2) n = occurs c n || occurs t1 n || occurs t2 n
occurs (Let _ _ _  t1 (Sc1 t2)) n = occurs t1 n || occurs t2 (n+1)

mapBound :: TTerm -> Int -> TTerm
mapBound v@(V i (Bound n)) n2 = if n > n2 then V i (Bound (n-1)) else v
mapBound v@(V _ _) _ = v
mapBound c@(Const _ _) _ = c
mapBound (Lam i x xty (Sc1 t)) n = Lam i x xty (Sc1 $ mapBound t (n+1)) 
mapBound (Print i str t) n = Print i str (mapBound t n)
mapBound (App i t1 t2) n = App i (mapBound t1 n) (mapBound t2 n)
mapBound (BinaryOp i op t1 t2) n = BinaryOp i op (mapBound t1 n) (mapBound t2 n)
mapBound (Fix i f fty x xty (Sc2 t)) n = Fix i f fty x xty (Sc2 $ mapBound t (n+2)) 
mapBound (IfZ i c t1 t2) n = IfZ i (mapBound c n) (mapBound t1 n) (mapBound t2 n)
mapBound (Let i x ty t1 (Sc1 t2)) n = Let i x ty (mapBound t1 n) (Sc1 $ mapBound t2 (n+1))

inline :: MonadFD4 m => TTerm -> [Name] -> [TTerm] -> m TTerm
inline v@(V _ _) _ _ = return v
inline c@(Const _ _ ) _ _ = return c
inline (Lam i x ty (Sc1 t)) ns env = do
    t' <- inline t (x:ns) env
    return $ Lam i x ty (Sc1 t') 
inline (Print i str t) ns env = do
    t' <- inline t ns env
    return $ Print i str t'
inline (BinaryOp i op t1 t2) ns env = do
    t1' <- inline t1 ns env
    t2' <- inline t2 ns env
    return $ BinaryOp i op t1' t2'
inline fx@(Fix i f fty x xty (Sc2 t)) ns env = return fx
inline (IfZ i c t1 t2) ns env = do
    c' <- inline c ns env
    t1' <- inline t1 ns env
    t2' <- inline t2 ns env
    return $ IfZ i c' t1' t2'
inline (Let i x ty t1 (Sc1 t2)) ns env = do
    t1' <- inline t1 (x:ns) env
    t2' <- inline t2 (x:ns) (t1:env)
    return $ Let i x ty t1' (Sc1 t2')
inline (App i v@(V _ (Global n)) t) ns env = do
    mtm <- lookupDecl n
    case mtm of
        Nothing -> failFD4 $ "Error de ejecución: variable no declarada: " ++ ppName n
        Just d -> if termHeuristic d > COST || isFix d then do
            t' <- inline t ns env
            return $ App i v t'
            else let decl = getScope d in case t of
                (V _ _) -> inline (subst t (Sc1 decl)) ns env
                (Const _ _) -> inline (subst t (Sc1 decl)) ns env
                _ -> let z = freshen ns n
                         zty = snd $ getInfo t in do
                    inline (Let i z zty t (Sc1 decl)) (z:ns) (t:env)
inline (App i v@(V _ (Bound idx)) t) ns env = let d = env !! idx in 
    if termHeuristic d > COST  || isFix d then do
        t' <- inline t ns env
        return $ App i v t'
    else let t' = getScope d in do
    case t of
        (V _ _) -> inline (subst t (Sc1 t')) ns env
        (Const _ _) -> inline (subst t (Sc1 t')) ns env
        _ -> let z = freshen ns "y"
                 zty = snd $ getInfo t in do
            inline (Let i z zty t (Sc1 t')) (z:ns) (t:env)
inline (App i t1 t2) ns env = do
    t1' <- inline t1 ns env
    t2' <- inline t2 ns env
    return $ App i t1' t2'

getScope :: TTerm -> TTerm
getScope (Lam _ _ _ (Sc1 t)) = t
getScope (Fix _ _ _ _ _ (Sc2 t)) = t
getScope t = t

isFix :: TTerm -> Bool
isFix (Fix _ _ _ _ _ _) = True
isFix t = False

termHeuristic :: TTerm -> Int
termHeuristic (V _ _) = 0
termHeuristic (Const _ _) = 0
termHeuristic (BinaryOp _ _ t1 t2) = 1 + termHeuristic t1 + termHeuristic t2
termHeuristic (Print _ _ t) = 1 + termHeuristic t 
termHeuristic (Lam _ _ _ (Sc1 t)) = 1 + termHeuristic t
termHeuristic (App _ t1 t2) = 1 + termHeuristic t1 + termHeuristic t2
termHeuristic (IfZ _ c t1 t2) = termHeuristic c + termHeuristic t1 + termHeuristic t2 + 1
termHeuristic (Fix _ _ _ _ _ (Sc2 t)) = 1 + termHeuristic t
termHeuristic (Let _ _ _ t1 (Sc1 t2)) = 1 + termHeuristic t1 + termHeuristic t2


-- getArgs :: TTerm -> Int -> [Int]
-- getArgs (Lam _ _ _ (Sc1 t)) = getArgs' t []
-- getArgs t = []

--getArgs' :: TTerm -> [Int] -> [Int] 

-- isInvariant :: TTerm -> Int -> Name -> Bool
-- isInvariant (V _ _) _  _ = True
-- isInvariant (Const _ _) _  _ = True
-- isInvariant (BinaryOp _ _ t1 t2) idx = case t1 of
--     (V _ (Bound i)) -> (i /= idx) && isInvariant t2 idx
--     _ -> case t2 of
--         (V _ (Bound i)) -> (i /= idx) && isInvariant t1 idx
--         _ -> isInvariant t1 idx && isInvariant t2 idx
-- isInvariant (Print _ _ t) idx = isInvariant t idx
-- isInvariant (Lam _ _ _ (Sc1 t)) idx = 1 + isInvariant t
-- isInvariant = 1 +isInvariant t1 + isInvariant t2
-- isInvariant (IfZ _ c t1 t2) = isInvariant c + isInvariant t1 + isInvariant t2 + 1
-- isInvariant (Fix _ _ _ _ _ (Sc2 t)) = 1 + isInvariant t
-- isInvariant (Let _ _ _ t1 (Sc1 t2)) = 1 + isInvariant t1 + isInvariant t2