{-# LANGUAGE RecordWildCards #-}

{-|
Module      : Main
Description : Compilador de FD4.
Copyright   : (c) Mauro Jaskelioff, Guido Martínez, 2020.
License     : GPL-3
Maintainer  : mauro@fceia.unr.edu.ar
Stability   : experimental

-}

module Main where

import System.Console.Haskeline ( defaultSettings, getInputLine, runInputT, InputT )
import Control.Monad.Catch (MonadMask)

import Control.Monad.Trans
import Data.List (nub, isPrefixOf, intercalate )
import Data.Char ( isSpace )
import Control.Exception ( catch , IOException )
import System.IO ( hPrint, stderr, hPutStrLn )
import Data.Maybe ( fromMaybe, isNothing, fromJust )

import System.Exit ( exitWith, ExitCode(ExitFailure) )
import Options.Applicative

import Global
import Errors
import Lang
import Parse ( P, tm, program, declOrTm, runP )
import Elab ( elab, typeElab, elabSDecl )
import Eval ( eval )
import PPrint ( pp , ppTy, ppDecl )
import MonadFD4
    ( when,
      void,
      MonadError(throwError),
      MonadState(get),
      gets,
      FD4,
      MonadFD4,
      getMode,
      getOpt,
      setInter,
      getInter,
      printFD4,
      setLastFile,
      getLastFile,
      addDecl,
      addTypeDecl,
      eraseLastFileDecls,
      lookupDecl,
      catchErrors,
      runFD4, runFD4Prof, FD4Prof )
import CEKMachine(evalCEK)
import TypeChecker ( tc, tcDecl )
import Bytecompile_8 (bytecompileModule, bcWrite, bcRead, runBC)
import Optimizer (optimize)
import ClosureConvert (ir2C2)
import System.FilePath (dropExtension)

prompt :: String
prompt = "FD4> "



-- | Parser de banderas
parseMode :: Parser (Mode,Bool,Bool)
parseMode = (,,) <$>
      (flag' Typecheck ( long "typecheck" <> short 't' <> help "Chequear tipos e imprimir el término")
      <|> flag' InteractiveCEK (long "interactiveCEK" <> short 'k' <> help "Ejecutar interactivamente en la CEK")
      <|> flag' Bytecompile (long "bytecompile" <> short 'm' <> help "Compilar a la BVM")
      <|> flag' RunVM (long "runVM" <> short 'r' <> help "Ejecutar bytecode en la BVM")
      <|> flag Interactive Interactive ( long "interactive" <> short 'i' <> help "Ejecutar en forma interactiva")
      <|> flag Eval        Eval        (long "eval" <> short 'e' <> help "Evaluar programa")
      <|> flag EvalCEK     EvalCEK     (long "cek" <> short 'v' <> help "Evaluar programa en la CEK")
      <|> flag' CC ( long "cc" <> short 'c' <> help "Compilar a código C")
  -- <|> flag' Canon ( long "canon" <> short 'n' <> help "Imprimir canonicalización")
  -- <|> flag' Assembler ( long "assembler" <> short 'a' <> help "Imprimir Assembler resultante")
  -- <|> flag' Build ( long "build" <> short 'b' <> help "Compilar")
      )
   -- <*> pure False
   -- reemplazar por la siguiente línea para habilitar opción
   <*> flag False True (long "optimize" <> short 'o' <> help "Optimizar código")
   <*> flag False True (long "profile" <> short 'p' <> help "Optimizar código")

-- | Parser de opciones general, consiste de un modo y una lista de archivos a procesar
parseArgs :: Parser (Mode,Bool,Bool,[FilePath])
parseArgs = (\(a,b,c) d -> (a,b,c,d)) <$> parseMode <*> many (argument str (metavar "FILES..."))

main :: IO ()
main = execParser opts >>= go
  where
    opts = info (parseArgs <**> helper)
      ( fullDesc
     <> progDesc "Compilador de FD4"
     <> header "Compilador de FD4 de la materia Compiladores 2023" )

    go :: (Mode,Bool,Bool,[FilePath]) -> IO ()
    go (Interactive,opt,False,files) =
              runOrFail (Conf opt Interactive False) (runInputT defaultSettings (repl files))
    go (InteractiveCEK,opt,False,files) =
              runOrFail (Conf opt InteractiveCEK False) (runInputT defaultSettings (repl files))
    go (Bytecompile,opt,False,files) =
              runOrFail (Conf opt Bytecompile False) (mapM_ compile files)
    go (RunVM,opt,False,files) =
              runOrFail (Conf opt RunVM False) (mapM_ runVM files)
    go (CC,opt,False,files) =
              runOrFailProf (Conf opt CC False) (mapM_ compile files)
    go (m,opt,False,files) =
              runOrFail (Conf opt m False) (mapM_ compile files)
    go (Interactive,opt,True,files) =
              runOrFailProf (Conf opt Interactive True) (runInputT defaultSettings (repl files))
    go (InteractiveCEK,opt,True,files) =
              runOrFailProf (Conf opt InteractiveCEK True) (runInputT defaultSettings (repl files))
    go (Bytecompile,opt,True,files) =
              runOrFailProf (Conf opt Bytecompile True) (mapM_ compile files)
    go (RunVM,opt,True,files) =
              runOrFailProf (Conf opt RunVM True) (mapM_ runVM files)
    go (CC,opt,True,files) =
              runOrFailProf (Conf opt CC True) (mapM_ compile files)
    go (m,opt,True,files) =
              runOrFailProf (Conf opt m True) (mapM_ compile files)


runOrFail :: Conf -> FD4 a -> IO a
runOrFail c m = do
  r <- runFD4 m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

runOrFailProf :: Conf -> FD4Prof a -> IO a
runOrFailProf c m = do
  r <- runFD4Prof m c
  case r of
    Left err -> do
      liftIO $ hPrint stderr err
      exitWith (ExitFailure 1)
    Right v -> return v

repl :: (MonadFD4 m, MonadMask m) => [FilePath] -> InputT m ()
repl args = do
       lift $ setInter True
       lift $ catchErrors $ mapM_ compile args
       s <- lift get
       when (inter s) $ liftIO $ putStrLn
         (  "Entorno interactivo para FD4.\n"
         ++ "Escriba :? para recibir ayuda.")
       loop
  where loop = do
           minput <- getInputLine prompt
           case minput of
               Nothing -> return ()
               Just "" -> loop
               Just x -> do
                       c <- liftIO $ interpretCommand x
                       b <- lift $ catchErrors $ handleCommand c
                       maybe loop (`when` loop) b

loadFile ::  MonadFD4 m => FilePath -> m [SDecl STerm STy]
loadFile f = do
    let filename = reverse(dropWhile isSpace (reverse f))
    x <- liftIO $ catch (readFile filename)
               (\e -> do let err = show (e :: IOException)
                         hPutStrLn stderr ("No se pudo abrir el archivo " ++ filename ++ ": " ++ err)
                         return "")
    setLastFile filename
    parseIO filename program x

compile :: MonadFD4 m => FilePath -> m ()
compile f = do
    i <- getInter
    setInter False
    when i $ printFD4 ("Abriendo "++f++"...")
    decls <- loadFile f
    mapM_ handleDecl decls
    m <- getMode
    case m of 
      Bytecompile -> do gdecl <- gets glb
                        bcode <- bytecompileModule (reverse gdecl)
                        liftIO $ bcWrite bcode (dropExtension f ++ ".bc8")
                        setInter i
      CC -> do gdecl <- gets glb
               code <- ir2C2 (reverse gdecl)
               liftIO $ writeFile (dropExtension f ++ ".c") code
               setInter i
      _ -> setInter i

runVM :: MonadFD4 m => FilePath -> m ()
runVM f = do
  bc <- liftIO $ bcRead f
  runBC bc

parseIO ::  MonadFD4 m => String -> P a -> String -> m a
parseIO filename p x = case runP p x filename of
                  Left e  -> throwError (ParseErr e)
                  Right r -> return r

evalDecl :: MonadFD4 m => SDecl STerm STy -> m (Maybe (Decl TTerm))
evalDecl d = 
  case d of
    (SType p n t) -> do
      nt <- typeElab p t
      addTypeDecl (n,addTyName nt n)
      return Nothing
    (SDecl p b bs t) -> do
      sd' <- elabSDecl p b bs t
      t'' <- elab $ sDeclBody sd'
      xty <- typeElab p $ snd $ head $ sDeclTy sd'
      (Decl p'' x xty' tt) <- tcDecl (Decl (sDeclPos sd') (fst $ head $ sDeclTy sd') xty t'')
      opt <- getOpt
      tt' <- if opt then optimize tt else return tt
      te <- evalTerm tt'
      addDecl (Decl p'' x xty' te)
      return (Just (Decl p'' x xty' te)) 
  where
    addTyName (NatTy _) n = NatTy (Just n)
    addTyName (FunTy _ t1 t2) n = FunTy (Just n) t1 t2 

putDecl :: MonadFD4 m => SDecl STerm STy -> m ()
putDecl d = 
  case d of
    (SType p n t) -> do
      nt <- typeElab p t
      addTypeDecl (n,addTyName nt n)
      return ()
    (SDecl p b bs t) -> do
      sd' <- elabSDecl p b bs t
      t'' <- elab $ sDeclBody sd'
      xty <- typeElab p $ snd $ head $ sDeclTy sd'
      (Decl p'' x xty' tt) <- tcDecl (Decl (sDeclPos sd') (fst $ head $ sDeclTy sd') xty t'')
      opt <- getOpt
      tt' <- if opt then optimize tt else return tt
      addDecl (Decl p'' x xty' tt')
  where
    addTyName (NatTy _) n = NatTy (Just n)
    addTyName (FunTy _ t1 t2) n = FunTy (Just n) t1 t2 


handleDecl ::  MonadFD4 m => SDecl STerm STy -> m ()
handleDecl d = do
        m <- getMode
        case m of
          Interactive -> void (evalDecl d)
          Eval -> void (evalDecl d)
          Typecheck -> do
              f <- getLastFile
              printFD4 ("Chequeando tipos de "++f)
              dcl <- evalDecl d
              if isNothing dcl 
                then return ()
                else do
                  ppterm <- ppDecl $ fromJust dcl
                  printFD4 ppterm
          InteractiveCEK -> void (evalDecl d)
          EvalCEK -> void (evalDecl d)
          Bytecompile -> putDecl d
          RunVM -> return ()
          CC -> putDecl d
  
             
data Command = Compile CompileForm
             | PPrint String
             | Type String
             | Reload
             | Browse
             | Quit
             | Help
             | Noop

data CompileForm = CompileInteractive  String
                 | CompileFile         String

data InteractiveCommand = Cmd [String] String (String -> Command) String

-- | Parser simple de comando interactivos
interpretCommand :: String -> IO Command
interpretCommand x
  =  if ":" `isPrefixOf` x then
       do  let  (cmd,t')  =  break isSpace x
                t         =  dropWhile isSpace t'
           --  find matching commands
           let  matching  =  filter (\ (Cmd cs _ _ _) -> any (isPrefixOf cmd) cs) commands
           case matching of
             []  ->  do  putStrLn ("Comando desconocido `" ++ cmd ++ "'. Escriba :? para recibir ayuda.")
                         return Noop
             [Cmd _ _ f _]
                 ->  do  return (f t)
             _   ->  do  putStrLn ("Comando ambigüo, podría ser " ++
                                   intercalate ", " ([ head cs | Cmd cs _ _ _ <- matching ]) ++ ".")
                         return Noop

     else
       return (Compile (CompileInteractive x))

commands :: [InteractiveCommand]
commands
  =  [ Cmd [":browse"]      ""        (const Browse) "Ver los nombres en scope",
       Cmd [":load"]        "<file>"  (Compile . CompileFile)
                                                     "Cargar un programa desde un archivo",
       Cmd [":print"]       "<exp>"   PPrint          "Imprime un término y sus ASTs sin evaluarlo",
       Cmd [":reload"]      ""        (const Reload)         "Vuelve a cargar el último archivo cargado",
       Cmd [":type"]        "<exp>"   Type           "Chequea el tipo de una expresión",
       Cmd [":quit",":Q"]        ""        (const Quit)   "Salir del intérprete",
       Cmd [":help",":?"]   ""        (const Help)   "Mostrar esta lista de comandos" ]

helpTxt :: [InteractiveCommand] -> String
helpTxt cs
  =  "Lista de comandos:  Cualquier comando puede ser abreviado a :c donde\n" ++
     "c es el primer caracter del nombre completo.\n\n" ++
     "<expr>                  evaluar la expresión\n" ++
     "let <var> = <expr>      definir una variable\n" ++
     unlines (map (\ (Cmd c a _ d) ->
                   let  ct = intercalate ", " (map (++ if null a then "" else " " ++ a) c)
                   in   ct ++ replicate ((24 - length ct) `max` 2) ' ' ++ d) cs)

-- | 'handleCommand' interpreta un comando y devuelve un booleano
-- indicando si se debe salir del programa o no.
handleCommand ::  MonadFD4 m => Command  -> m Bool
handleCommand cmd = do
   s@GlEnv {..} <- get
   case cmd of
       Quit   ->  return False
       Noop   ->  return True
       Help   ->  printFD4 (helpTxt commands) >> return True
       Browse ->  do  printFD4 (unlines (reverse (nub (map declName glb))))
                      return True
       Compile c ->
                  do  case c of
                          CompileInteractive e -> compilePhrase e
                          CompileFile f        -> compile f
                      return True
       Reload ->  eraseLastFileDecls >> (getLastFile >>= compile) >> return True
       PPrint e   -> printPhrase e >> return True
       Type e    -> typeCheckPhrase e >> return True

compilePhrase ::  MonadFD4 m => String -> m ()
compilePhrase x = do
    dot <- parseIO "<interactive>" declOrTm x
    case dot of
      Left d  -> handleDecl d
      Right t -> handleTerm t

handleTerm ::  MonadFD4 m => STerm -> m ()
handleTerm t = do
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         opt <- getOpt
         tt' <- if opt then optimize tt else return tt
         te <- evalTerm tt'
         ppte <- pp te
         printFD4 (ppte ++ " : " ++ ppTy (getTy tt'))

printPhrase   :: MonadFD4 m => String -> m ()
printPhrase x =
  do
    x' <- parseIO "<interactive>" tm x
    ex <- elab x'
    tyenv <- gets tyEnv
    tex <- tc ex tyenv
    t  <- case x' of
           (SV p f) -> fromMaybe tex <$> lookupDecl f
           _       -> return tex
    printFD4 "STerm:"
    printFD4 (show x')
    printFD4 "TTerm:"
    printFD4 (show t)

typeCheckPhrase :: MonadFD4 m => String -> m ()
typeCheckPhrase x = do
         t <- parseIO "<interactive>" tm x
         t' <- elab t
         s <- get
         tt <- tc t' (tyEnv s)
         let ty = getTy tt
         printFD4 (ppTy ty)


evalTerm :: MonadFD4 m => TTerm -> m TTerm
evalTerm t = do 
  m <- getMode
  case m of
    Interactive -> eval t
    InteractiveCEK -> evalCEK t
    Eval -> eval t
    Typecheck -> eval t
    EvalCEK -> evalCEK t
    CC -> eval t
    _ -> eval t