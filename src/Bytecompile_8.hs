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
module Bytecompile_8
  (Bytecode, runBC, bcWrite, bcRead, bytecompileModule, showBC)
 where

import Lang
import MonadFD4 ( MonadFD4, printFD4, failFD4,tick, addClos, updateStackSize, gets, getProfile )

import qualified Data.ByteString.Lazy as BS
import Data.Binary ( Binary(put, get), decode, encode, Word8 )
import Data.Binary.Put ( putWord8 )
import Data.Binary.Get ( getWord8, isEmpty )
import Subst(close)
import qualified Data.ByteString.UTF8 as UTF8
import Data.List (intercalate)
import Data.Char
import Data.Bits ((.&.),(.|.),shiftR,shiftL)
import Control.Monad ( void, when )
import Global
import qualified Data.ByteString as UTF8

type Bytecode = [Int]
newtype Bytecode8 = BC { un8 :: [Word8] }

{- Esta instancia explica como codificar y decodificar Bytecode de 32 bits -}
instance Binary Bytecode8 where
  put (BC bs) = mapM_ putWord8 bs
  get = go
    where go =
           do
            empty <- isEmpty
            if empty
              then return $ BC []
              else do x <- getWord8
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

pattern NULL_8 :: Word8
pattern NULL_8 = 0x00
pattern RETURN_8 :: Word8
pattern RETURN_8 = 0x01
pattern CONST_8 :: Word8
pattern CONST_8   = 0x02
pattern ACCESS_8 :: Word8
pattern ACCESS_8   = 0x03
pattern FUNCTION_8 :: Word8
pattern FUNCTION_8 = 0x04
pattern CALL_8 :: Word8
pattern CALL_8    = 0x05
pattern ADD_8 :: Word8
pattern ADD_8      = 0x06
pattern SUB_8 :: Word8
pattern SUB_8      = 0x07
pattern CJUMP_8 :: Word8
pattern CJUMP_8    = 0x08
pattern FIX_8 :: Word8
pattern FIX_8      = 0x09
pattern STOP_8 :: Word8
pattern STOP_8     = 0x0A
pattern SHIFT_8 :: Word8
pattern SHIFT_8    = 0x0B
pattern DROP_8 :: Word8
pattern DROP_8     = 0x0C
pattern PRINT_8 :: Word8
pattern PRINT_8    = 0x0D
pattern PRINTN_8 :: Word8
pattern PRINTN_8   = 0x0E
pattern JUMP_8 :: Word8
pattern JUMP_8     = 0x0F
pattern TAILCALL_8 :: Word8
pattern TAILCALL_8 = 0x10

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
bcc (V _ (Bound n)) = return [ACCESS, n]
bcc (V _ (Free n)) = failFD4 "Error Free"
bcc (V _ (Global n)) = failFD4 "Error Global"
bcc (Const _ (CNat n)) = return [CONST,n]
bcc (Lam _ _ _ (Sc1 t)) = do
  t' <- bct t
  return $ [FUNCTION,length t'] ++ t'
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
  return $ [FUNCTION,length t'] ++ t' ++ [FIX]
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
  return $ c' ++ [CJUMP,length t'] ++ t' ++ t''
bct (Let _ _ _ t1 (Sc1 t2)) = do
  t' <- bcc t1
  t'' <- bct t2
  return $ t' ++ [SHIFT] ++ t''
bct t = do
  t' <- bcc t
  return $ t' ++ [RETURN]

int2Word8 :: Int -> [Word8]
int2Word8 n = [ fromIntegral (n .&. 0xFF)
  , fromIntegral (n `shiftR` 8 .&. 0xFF)
  , fromIntegral (n `shiftR` 16 .&. 0xFF)
  , fromIntegral (n `shiftR` 24 .&. 0xFF)
  ]

bc2Word8 :: Bytecode -> [Word8]
bc2Word8 [] = []
bc2Word8 (CONST:n:bs) = CONST_8:int2Word8 n ++ bc2Word8 bs 
bc2Word8 (ACCESS:n:bs) = ACCESS_8:int2Word8 n ++ bc2Word8 bs
bc2Word8 (ADD:bs) = ADD_8:bc2Word8 bs
bc2Word8 (SUB:bs) = SUB_8:bc2Word8 bs
bc2Word8 (CJUMP:n:bs) = CJUMP_8:int2Word8 n ++ bc2Word8 bs
bc2Word8 (JUMP:n:bs) = JUMP_8:int2Word8 n ++ bc2Word8 bs
bc2Word8 (FIX:bs) = FIX_8:bc2Word8 bs
bc2Word8 (STOP:bs) = STOP_8:bc2Word8 bs
bc2Word8 (SHIFT:bs) = SHIFT_8:bc2Word8 bs
bc2Word8 (DROP:bs) = DROP_8:bc2Word8 bs
bc2Word8 (TAILCALL:bs) = TAILCALL_8:bc2Word8 bs
bc2Word8 (PRINT:bs) = 
  let (str,bs') = span (/= NULL) bs
      str' = UTF8.unpack $ UTF8.fromString $ bc2string str
  in PRINT_8:str' ++ bc2Word8 bs'
bc2Word8 (PRINTN:bs) = PRINTN_8:bc2Word8 bs
bc2Word8 (CALL:bs)  = CALL_8:bc2Word8 bs 
bc2Word8 (RETURN:bs)  = RETURN_8:bc2Word8 bs 
bc2Word8 (NULL:bs)  = NULL_8:bc2Word8 bs 
bc2Word8 (FUNCTION:n:bs)  = FUNCTION_8:int2Word8 n ++ bc2Word8 bs
bc2Word8 _ = undefined

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
bytecompileModule m = do
  t' <- bcc2 $ module2Term m
  return $ t' ++ [STOP]

-- | Toma un bytecode, lo codifica y lo escribe un archivo
bcWrite :: Bytecode -> FilePath -> IO ()
bcWrite bs filename = BS.writeFile filename (encode $ BC $ bc2Word8 bs)

---------------------------
-- * Ejecución de bytecode
---------------------------
word8ToInt :: [Word8] -> Int
word8ToInt [b1,b2,b3,b4] =
  let b1' = fromIntegral b1
      b2' = fromIntegral b2
      b3' = fromIntegral b3
      b4' = fromIntegral b4
  in b4' `shiftL` 24 .|. b3' `shiftL` 16 .|. b2' `shiftL` 8 .|. b1'
word8ToInt _ = undefined

word8ToBytecode :: [Word8] -> Bytecode
word8ToBytecode [] = []
word8ToBytecode (CONST_8:bs) = 
  let (ns,bs') = splitAt 4 bs
      n = word8ToInt ns
  in CONST:n:word8ToBytecode bs' 
word8ToBytecode (ACCESS_8:bs) =
  let (ns,bs') = splitAt 4 bs
      n = word8ToInt ns
  in ACCESS:n:word8ToBytecode bs' 
word8ToBytecode (ADD_8:bs) = ADD:word8ToBytecode bs
word8ToBytecode (SUB_8:bs) = SUB:word8ToBytecode bs
word8ToBytecode (CJUMP_8:bs) = 
  let (ns,bs') = splitAt 4 bs
      n = word8ToInt ns
  in CJUMP:n:word8ToBytecode bs' 
word8ToBytecode (JUMP_8:bs) = 
  let (ns,bs') = splitAt 4 bs
      n = word8ToInt ns
  in JUMP:n:word8ToBytecode bs' 
word8ToBytecode (FIX_8:bs) = FIX:word8ToBytecode bs
word8ToBytecode (STOP_8:bs) = STOP:word8ToBytecode bs
word8ToBytecode (SHIFT_8:bs) = SHIFT:word8ToBytecode bs
word8ToBytecode (DROP_8:bs) = DROP:word8ToBytecode bs
word8ToBytecode (TAILCALL_8:bs) = TAILCALL:word8ToBytecode bs
word8ToBytecode (PRINT_8:bs) = 
  let (str,bs') = span (/= NULL_8) bs
      str' = string2bc $ UTF8.toString $ UTF8.pack str
  in PRINT:str' ++ word8ToBytecode bs'
word8ToBytecode (PRINTN_8:bs) = PRINTN:word8ToBytecode bs
word8ToBytecode (CALL_8:bs)  = CALL:word8ToBytecode bs 
word8ToBytecode (RETURN_8:bs)  = RETURN:word8ToBytecode bs 
word8ToBytecode (NULL_8:bs)  = NULL:word8ToBytecode bs 
word8ToBytecode (FUNCTION_8:bs)  = 
  let (ns,bs') = splitAt 4 bs
      n = word8ToInt ns
  in FUNCTION:n:word8ToBytecode bs' 
word8ToBytecode _ = undefined


-- | Lee de un archivo y lo decodifica a bytecode
bcRead :: FilePath -> IO Bytecode
bcRead filename = (word8ToBytecode <$> un8) . decode <$> BS.readFile filename

runBC :: MonadFD4 m => Bytecode -> m ()
runBC bc = do
  runBC' bc [] []
  p <- getProfile
  when p $ do
    c <- gets count
    st <- gets stackSize
    clos <- gets numClosures
    printFD4 $ "Cantidad de operaciones ejecutadas : " ++ show c
    printFD4 $ "Tamano maximo del stack : " ++ show st
    printFD4 $ "Cantidad de clausuras creadas : " ++ show clos

runBC' :: MonadFD4 m => Bytecode -> Env -> [Val] -> m ()
runBC' (STOP:_) _ _ = void tick
runBC' (CONST:n:bs) e s = tick >> updateStackSize (I n:s) >> runBC' bs e (I n:s)
runBC' (SUB:bs) e (I x1:I x2:s) =
  let res = max 0 (x2-x1)
  in tick >> updateStackSize (I res:s) >>  runBC' bs e (I res:s)
runBC' (ADD:bs) e ((I x1):(I x2):s) = tick >> runBC' bs e (I (x2+x1):s)
runBC' (ACCESS:i:bs) e s = tick >> updateStackSize ((e!!i):s) >> runBC' bs e ((e!!i):s)
runBC' (CALL:bs) e (v:(Fun e' bs'):s) = tick >> updateStackSize (RA e bs:s) >> runBC' bs' (v:e') (RA e bs:s)
runBC' (FUNCTION:n:bs) e s =
  let (cf,c) = splitAt n bs
  in tick >> addClos >> updateStackSize (Fun e cf:s) >> runBC' c e (Fun e cf:s)
runBC' (RETURN:_) _ (v:(RA e bs):s) = tick >> runBC' bs e (v:s)
runBC' (SHIFT:bs) e (v:s) = tick >> runBC' bs (v:e) s
runBC' (DROP:bs) (v:e) s = tick >> runBC' bs e s
runBC' (JUMP:n:bs) e s =
  let bs' = drop n bs
  in tick >> runBC' bs' e s
runBC' (PRINTN:bs) e ((I n):s) = do
    printFD4 (show n)
    tick
    runBC' bs e (I n:s)
runBC' (PRINT:bs) e ((I n):s) =
  let (str,bs') = span (/= NULL) bs
      str' = bc2string str
  in do
    printFD4 (str'++show n)
    tick
    tick
    runBC' (drop 2 bs') e (I n:s)
runBC' (FIX:bs) e (Fun _ cf:s) =
  let efix = Fun efix cf : e
  in tick >> addClos >> runBC' bs e (Fun efix cf:s)
runBC' (CJUMP:n:bs) e (I m:s) = if m == 0
  then tick >> runBC' bs e s
  else tick >> runBC' (drop n bs) e s
runBC' (TAILCALL:bs) _ (v:Fun e' bs':s) = tick >> runBC' bs' (v:e') s
runBC' (b:_) _ _ = failFD4 $ "Instrucción inválida: " ++ show b
runBC' _ _ _ = failFD4 "Error inesperado"