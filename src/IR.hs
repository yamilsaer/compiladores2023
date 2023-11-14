module IR where

import Lang ( Name, Const, BinaryOp )
import Control.Monad.State.Lazy (State,runState)

data Ir = IrVar Name IrTy
        | IrGlobal Name
        | IrCall Ir [Ir] IrTy
                        -- ^ Tipo de expr final
        | IrConst Const
        | IrPrint String Ir
        | IrBinaryOp BinaryOp Ir Ir 
        | IrLet Name IrTy Ir Ir
        | IrIfZ Ir Ir Ir
        | MkClosure Name [Ir]
        | IrAccess Ir IrTy Int
  deriving Show

data IrTy = IrInt
          | IrClo
          | IrFunTy
  deriving Show

data IrDecl =
    IrFun { irDeclName :: Name
          , irRetTy :: IrTy
          , irDeclArgs :: [(Name, IrTy)]
          , irDeclBody :: Ir
    }
  | IrVal { irDeclName :: Name
          , irDeclTy :: IrTy
          , irDeclDef :: Ir
          }
  deriving Show

newtype IrDecls = IrDecls { irDecls :: [IrDecl] }

{-
La siguiente instancia es sólo para debugging
-}
instance Show IrDecls where
  show (IrDecls decls) =
   concatMap (\d -> show d ++ "\n") decls

type IR = State StateIr

data StateIr = StateIr { 

  freshIndex :: Int,
  idecls :: [IrDecl],
  freshName :: Name,
  lastVar :: [Ir], -- Lista de variables libres
  lastClosure :: Name -- Nombre de la ultima clausura
}

runIR :: IR a -> Name -> (a,StateIr)
runIR c n = runState c (initState n)

initState :: Name -> StateIr
initState n = StateIr 0 [] n [] ""