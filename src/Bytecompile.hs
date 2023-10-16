{-# LANGUAGE PatternSynonyms #-}
--{-# LANGUAGE RecordWildCards #-}
{-|
Module      : Bytecompile
Description : Compila a bytecode. Ejecuta bytecode.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

Este módulo permite compilar módulos a la Macchina. También provee
una implementación de la Macchina para ejecutar el bytecode.
-}
module Bytecompile
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import MonadFD4

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Word32, Binary(put, get), decode, encode )
import Data.Binary.Put ( putWord32le )
import Data.Binary.Get ( getWord32le, isEmpty )
import Subst(close)
import Data.List (intercalate)
import Data.Char

type Opcode = Int
type Bytecode = [Int]

newtype Bytecode32 = BC { un32 :: [Word32] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode32 where
  put (BC bs) = mapM_ putWord32le bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord32le
                      BC xs <- go
                      return $ BC (x:xs)

{- Estos sinónimos de patrón nos permiten escribir y hacer
pattern-matching sobre el nombre de la operación en lugar del código
entero, por ejemplo:

   f (CALL : cs) = ...

 Notar que si hubieramos escrito algo como
   call = 5
 no podríamos hacer pattern-matching con `call`.

 En lo posible, usar estos códigos exactos para poder ejectutar un
 mismo bytecode compilado en distintas implementaciones de la máquina.
-}
pattern NULL :: Int
pattern NULL     = 0
pattern RETURN :: Int
pattern RETURN   = 1
pattern CONST :: Int
pattern CONST    = 2
pattern ACCESS :: Int
pattern ACCESS   = 3
pattern FUNCTION :: Int
pattern FUNCTION = 4
pattern CALL :: Int
pattern CALL     = 5
pattern ADD :: Int
pattern ADD      = 6
pattern SUB :: Int
pattern SUB      = 7
pattern CJUMP :: Int
pattern CJUMP    = 8
pattern FIX :: Int
pattern FIX      = 9
pattern STOP :: Int
pattern STOP     = 10
pattern SHIFT :: Int
pattern SHIFT    = 11
pattern DROP :: Int
pattern DROP     = 12
pattern PRINT :: Int
pattern PRINT    = 13
pattern PRINTN :: Int
pattern PRINTN   = 14
pattern JUMP :: Int
pattern JUMP     = 15
pattern TAILCALL :: Int
pattern TAILCALL = 16
pattern SDROP :: Int
pattern SDROP = 17

data Val = I Int | Fun Env Bytecode | RA Env Bytecode deriving Show
type Env = [Val]

--función util para debugging: muestra el Bytecode de forma más legible.
showOps :: Bytecode -> [String]
showOps [] = []
showOps (NULL:xs)        = "NULL" : showOps xs
showOps (RETURN:xs)      = "RETURN" : showOps xs
showOps (CONST:i:xs)     = ("CONST " ++  show i) : showOps xs
showOps (ACCESS:i:xs)    = ("ACCESS " ++ show i) : showOps xs
showOps (FUNCTION:i:xs)  = ("FUNCTION len=" ++ show i) : showOps xs
showOps (CALL:xs)        = "CALL" : showOps xs
showOps (ADD:xs)         = "ADD" : showOps xs
showOps (SUB:xs)         = "SUB" : showOps xs
showOps (FIX:xs)         = "FIX" : showOps xs
showOps (STOP:xs)        = "STOP" : showOps xs
showOps (JUMP:i:xs)      = ("JUMP off=" ++ show i) : showOps xs
showOps (CJUMP:i:xs)      = ("CJUMP off=" ++ show i) : showOps xs
showOps (SHIFT:xs)       = "SHIFT" : showOps xs
showOps (DROP:xs)        = "DROP" : showOps xs
showOps (PRINT:xs)       = let (msg,_:rest) = span (/=NULL) xs
                           in ("PRINT " ++ show (bc2string msg)) : showOps rest
showOps (PRINTN:xs)      = "PRINTN" : showOps xs
showOps (TAILCALL:xs)    = "TAILCALL" : showOps xs
showOps (x:xs)           = show x : showOps xs

showBC :: Bytecode -> String
showBC = intercalate "; " . showOps

-- bcc2 elimina los drops antes del STOP, ya que no hace falta evaluarlos.
bcc2 :: MonadFD4 m => TTerm -> m Bytecode
bcc2 (Let _ _ _ t1 (Sc1 t2)) = do
  t' <- bcc t1
  t'' <- bcc2 t2
  return $ t' ++ [SHIFT] ++ t''
bcc2 t = bcc t

bcc :: MonadFD4 m => TTerm -> m Bytecode
bcc (V _ (Bound n)) = return [ACCESS,n]
bcc (V _ (Free n)) = failFD4 "Error Free"
bcc (V _ (Global n)) = failFD4 "Error Global"
bcc (Const _ (CNat n)) = return [CONST,n]
bcc (Lam _ _ _ (Sc1 t)) = do
  t' <- bct t
  return $ [FUNCTION,length t'+1] ++ t'
bcc (App _ t1 t2) = do
  t' <- bcc t1
  t'' <- bcc t2
  return $ t' ++ t'' ++ [CALL]
bcc (Print _ str t) = do
  t' <- bcc t
  return $ t' ++ PRINT:string2bc str ++ [NULL,PRINTN]
bcc (BinaryOp _ op t1 t2) = do
  t' <- bcc t1
  t'' <- bcc t2
  case op of
    Add -> return $ t' ++ t'' ++ [ADD]
    Sub -> return $ t' ++ t'' ++ [SUB]
bcc (Fix _ _ _ _ _ (Sc2 t)) = do
  t' <- bct t
  return $ [FUNCTION,length t'+1] ++ t' ++ [FIX]
bcc (IfZ _ c t1 t2) = do
  c' <- bcc c
  t' <- bcc t1
  t'' <- bcc t2
  return $ c' ++ [CJUMP,length t'+ 2] ++ t' ++ [JUMP,length t''] ++ t''
bcc (Let _ _ _ t1 (Sc1 t2)) = do
  t' <- bcc t1
  t'' <- bcc t2
  return $ t' ++ [SHIFT] ++ t'' ++ [DROP]

bct :: MonadFD4 m => TTerm -> m Bytecode
bct (App _ t1 t2) = do
  t' <- bcc t1
  t'' <- bcc t2
  return $ t' ++ t'' ++ [TAILCALL]
bct (IfZ _ c t1 t2) = do
  c' <- bcc c
  t' <- bct t1
  t'' <- bct t2
  return $ c' ++ [CJUMP,length t'+ 2] ++ t' ++ [JUMP,length t''] ++ t''
bct (Let _ _ _ t1 (Sc1 t2)) = do
  t' <- bcc t1
  t'' <- bct t2
  return $ t' ++ [SHIFT] ++ t''
bct t = do
  t' <- bcc t
  return $ t' ++ [RETURN]

-- ord/chr devuelven los codepoints unicode, o en otras palabras
-- la codificación UTF-32 del caracter.
string2bc :: String -> Bytecode
string2bc = map ord

bc2string :: Bytecode -> String
bc2string = map chr

global2Free :: TTerm -> TTerm
global2Free (V i (Global n)) = V i (Free n)
global2Free t@(V _ _) = t
global2Free t@(Const _ _) =  t
global2Free (Lam i n ty (Sc1 t)) = Lam i n ty (Sc1 $ global2Free t)
global2Free (App i t1 t2) = App i (global2Free t1) (global2Free t2)
global2Free (Print i str t) = Print i str (global2Free t)  
global2Free (BinaryOp i op t1 t2) = BinaryOp i op (global2Free t1) (global2Free t2)
global2Free (Fix i f fty x xty (Sc2 t)) = Fix i f fty x xty (Sc2 (global2Free t))
global2Free (IfZ i c t1 t2) = IfZ i (global2Free c) (global2Free t1) (global2Free t2)
global2Free (Let i n ty t1 (Sc1 t2)) = Let i n ty (global2Free t1) (Sc1 $ global2Free t2)

module2Term :: Module -> TTerm
module2Term [Decl i n ty body] = global2Free body
module2Term (Decl i n ty body:ds) = 
  let body' = module2Term ds
  in Let (i,ty) n ty body (close n $ global2Free body')
module2Term [] = undefined

bytecompileModule :: MonadFD4 m => Module -> m Bytecode
bytecompileModule m = 
  let t = module2Term m
  in do
    t' <- bcc2 t
    return $ t' ++ [STOP]

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ fromIntegral <$> bs)

---------------------------
-- * Ejecución de bytecode
---------------------------

-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (map fromIntegral <$> un32) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = runBC' bc [] []

runBC' :: MonadFD4 m => Bytecode -> Env -> [Val] -> m ()
runBC' (STOP:_) _ _ = return ()
runBC' (CONST:n:bs) e s = runBC' bs e (I n:s)
runBC' (SUB:bs) e (I x1:I x2:s) = 
  let res = max 0 (x2-x1)
  in runBC' bs e (I res:s)
runBC' (ADD:bs) e ((I x1):(I x2):s) = runBC' bs e (I (x2+x1):s)
runBC' (ACCESS:i:bs) e s = runBC' bs e ((e!!i):s)
runBC' (CALL:bs) e (v:(Fun e' bs'):s) = runBC' bs' (v:e') (RA e bs:s)
runBC' (FUNCTION:n:bs) e s =
  let (cf,c) = splitAt n bs
  in runBC' c e (Fun e cf:s)
runBC' (RETURN:_) _ (v:(RA e bs):s) = runBC' bs e (v:s)
runBC' (SHIFT:bs) e (v:s) = runBC' bs (v:e) s
runBC' (DROP:bs) (v:e) s = runBC' bs e s
runBC' (JUMP:n:bs) e s = 
  let bs' = drop n bs 
  in runBC' bs' e s
runBC' (PRINTN:bs) e ((I n):s) = do
    printFD4 (show n)
    runBC' bs e (I n:s)
runBC' (PRINT:bs) e ((I n):s) =
  let (str,bs') = span (/= NULL) bs
      str' = bc2string str
  in do
    printFD4 (str'++show n)
    runBC' (drop 2 bs') e (I n:s)
runBC' (FIX:bs) e (Fun _ cf:s) = 
  let efix = Fun efix cf : e
  in runBC' bs e (Fun efix cf:s)
runBC' (CJUMP:n:bs) e (I m:s) = if m == 0
  then runBC' bs e s
  else runBC' (drop n bs) e s
runBC' (TAILCALL:bs) _ (v:Fun e' bs':s) = runBC' bs' (v:e') s
runBC' (SDROP:bs) e (v:s) = runBC' bs e s
runBC' (b:_) _ _ = failFD4 $ "Instrucción inválida: " ++ show b
runBC' _ _ _ = failFD4 "Error inesperado"