

{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}


import Unbound.LocallyNameless

--import Control.Applicative
import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Trans.Maybe
import Data.List as L
import Data.Set as S
import Data.Maybe
-- import Control.Monad.Trans.Error

import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec ((<|>),many)
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (render,(<+>),hsep,punctuate,brackets,(<>),text,Doc)

data Channel 
type ChName = Name Channel



type EqnName = Name GoType


data GoType = Send ChName GoType
            | Recv ChName GoType
            | Tau GoType
            | IChoice GoType GoType -- Just two things?
            | OChoice [GoType]
            | Par [GoType]
            | New (Bind ChName GoType)
            | Null
            | Close ChName GoType
            | TVar EqnName
            | ChanInst GoType [ChName] -- P(c)
            | ChanAbst (Bind [ChName] GoType) -- \c.P
    deriving Show



data Eqn = EqnSys (Bind (Rec [(EqnName , Embed GoType)]) GoType)
    deriving Show
-- inner Proc will always be ChanAbst
             
$(derive [''Channel,''GoType,''Eqn])

--instance Alpha Channel
instance Alpha GoType
instance Alpha Eqn

instance Subst GoType Eqn
--instance Subst String GoType
--instance Subst String Eqn

instance Subst GoType GoType where
  isvar (TVar x) = Just (SubstName x)
  isvar _ = Nothing

type M a = FreshM a

-- Free name/var wrappers --
fnTyp :: GoType -> [ChName]
fnTyp t = fv t

fvTyp :: GoType -> [EqnName]
fvTyp t = fv t

fnEqn :: Eqn -> [ChName]
fnEqn e = fv e

fvEqn :: Eqn -> [EqnName]
fvEqn e = fv e


-- GoType Combinators (TVars, New, Chan Abs and Inst) --
tvar :: String -> GoType
tvar = TVar . s2n

new :: String -> GoType -> GoType
new s t = New $ bind (s2n s) t

chanAbst :: String -> GoType -> GoType
chanAbst s t = ChanAbst $ bind ([s2n s]) t

chanAbstL :: [String] -> GoType -> GoType
chanAbstL l t = ChanAbst $ bind (L.map s2n l) t

chanInst :: String -> String -> GoType
chanInst s c = ChanInst (tvar s) ([s2n c])

chanInstL :: String -> [String] -> GoType
chanInstL s l = ChanInst (tvar s) (L.map s2n l)

------------------------------

-- Equation System Combinators --

eqn' :: String -> GoType -> GoType -> Eqn
eqn' s t1 t2 = EqnSys (bind (rec [(s2n s , Embed(t1) )]) t2)

eqn :: String -> String -> GoType -> GoType -> Eqn
eqn s c t1 t2 = eqn' s (chanAbst c t1) t2



eqnl :: [(String,[String],GoType)] -> GoType -> Eqn
eqnl l t = EqnSys (bind (rec (L.map (\(var,plist,def) -> 
                     (s2n var , Embed(chanAbstL plist def))
                     ) l)) t) 

----------------------------------------

-- Structural Congruence --

-- Flatten out Pars in Par (i.e. T | (S | R) == (T | S) | R)--
flattenPar :: GoType -> GoType
flattenPar (Par l) = Par (flattenPar' l)
    where flattenPar' (x:xs) = 
                      case x of
                        Par l -> (flattenPar x):(flattenPar' xs)
                        _ -> x:(flattenPar' xs)  
          flattenPar' [] = []
flattenPar t = t

-- Remove Nulls from Par (i.e.  T | 0 == T)--
gcNull :: GoType -> GoType
gcNull (Par l) = let res = gcNull' l in 
       if (L.null res) then Null else Par res
  where gcNull' (x:xs) =
                case x of 
                     Null -> gcNull' xs
                     _ -> x:(gcNull' xs)
        gcNull' [] = []
gcNull t = t

-- GC unused bound names --
gcBNames' :: GoType -> M GoType
gcBNames' (Send c t) = do
  t' <- gcBNames' t
  return $ Send c t'
gcBNames' (Recv c t) = do
  t' <- gcBNames' t
  return $ Recv c t'
gcBNames' (Tau t) = do
  t' <- gcBNames' t
  return $ Tau t'
gcBNames' (IChoice t1 t2) = do
  t1' <- gcBNames' t1
  t2' <- gcBNames' t2
  return $ IChoice t1' t2'
gcBNames' (OChoice l) = do
 lm' <- mapM gcBNames' l
 return $ OChoice lm'
gcBNames' (Par l) = do
 lm' <- mapM gcBNames' l
 return $ Par lm'
gcBNames' (New bnd) = do
  (c,t) <- unbind bnd
  t' <- gcBNames' t
  -- GC if c not used
  if c `S.notMember` fv t'
    then return t'
    else return (New (bind c t'))                              
gcBNames' (Null) = return Null
gcBNames' (Close c t) = do
  t' <- gcBNames' t
  return $ Close c t'
gcBNames' (TVar x) = return $ TVar x
gcBNames' (ChanInst t lc) = do  -- P(~c)
  t' <- gcBNames' t
  return $ ChanInst t' lc
gcBNames' (ChanAbst bnd) = do
  (c,t) <- unbind bnd
  t' <- gcBNames' t
  return $ ChanAbst (bind c t')
  

gcBNames :: GoType -> GoType
gcBNames = runFreshM . gcBNames'







-- Open top-level bound names in a list of parallel types --
-- return is a list of (mc,t) where mc is Nothing if t is
-- closed and Just(c) otherwise.
openBNames :: [GoType] -> M [(Maybe ChName,GoType)]
openBNames l = do
  res <- openBNames' l
  return $ (init res)

openBNames' (x:xs) =
  case x of
   New bnd -> do
     (c,t) <- unbind bnd
     rest <- openBNames' xs
     return $ (Just(c),t):rest
   _ -> do
     res <- openBNames' xs
     return $ (Nothing,x):res
openBNames' [] = return $ [(Nothing,Null)]

-- Reconstructs the appropriate GoType from calls
-- to openBNames
closeBNames ::  M [(Maybe ChName,GoType)] -> M GoType
closeBNames m  = do
  l <- m
  let (names,ts) = unzip l
  return $ L.foldr (\mc end ->
                    case mc of
                      Just(c) -> New (bind c end)
                      Nothing -> end) (Par ts) names

-- Composes open/close and escapes the freshness monad --
pullBNamesPar :: GoType -> GoType
pullBNamesPar (Par l) =
  runFreshM (closeBNames . openBNames $ l)
pullBNamesPar t = t 

  
nf :: GoType -> GoType
nf = id

structCong :: GoType -> GoType -> Bool
structCong t1 t2 = (nf t1) `aeq` (nf t2)


-----------


-- Pretty Printing --

class Pretty p where
  ppr :: (Applicative m, LFresh m) => p -> m Doc

instance Pretty (Name a) where
  ppr = return . text . show

dot = text "."
bang = text "!"
qmark = text "?"
oplus = text "+"
amper = text "&"
tau = text "tau"

instance Pretty GoType where
  ppr (Send c t) = do
   t' <- ppr t
   c' <- ppr c
   return $ c' <> bang <> PP.semi <> t'
  ppr (Recv c t) = do
   t' <- ppr t
   c' <- ppr c
   return $ c' <> qmark <> PP.semi <> t'
  ppr (Tau t) = do
   t' <- ppr t
   return $ tau <> PP.semi <> t'
  ppr (IChoice t1 t2) = do
   t1' <- ppr t1
   t2' <- ppr t2
   return $ oplus <> PP.braces (t1' <+> PP.comma <+> t2')
  ppr (OChoice l) = do
   l' <- mapM ppr l
   let prettyl = punctuate PP.comma l'
   return $ amper <> PP.braces (hsep prettyl)
  ppr (Par l) = do
   l' <- mapM ppr l
   let prettyl = punctuate (PP.text "|") l'
   return $ (hsep prettyl)
  ppr (New bnd) = lunbind bnd $ \(c,t) -> do
      c' <- ppr c
      t' <- ppr t
      return $ PP.text "new" <+> c' <> dot <> (PP.parens t')
  ppr (Null) = return $ text "0"
  ppr (Close c t) = do
      t' <- ppr t
      c' <- ppr c
      return $ PP.text "close " <> c' <> PP.semi <> t'
  ppr (TVar x) = ppr x
  ppr (ChanInst t plist) = do
      t' <- ppr t
      l' <- mapM ppr plist
      let plist' = punctuate PP.comma l'
      return $ t' <+> PP.char '<' <> (hsep plist') <> PP.char '>'
  ppr (ChanAbst bnd) = lunbind bnd $ \(lc,t) -> do
      t' <- ppr t
      l' <- mapM ppr lc
      let plist' = punctuate PP.comma l'
      return $ brackets (hsep plist') <+> t'

instance Pretty Eqn where
  ppr (EqnSys bnd) = lunbind bnd $ \(r,t) -> do
      t' <- ppr t
      let defs = unrec r
      pdefs <- mapM (\(n,Embed(t0)) -> do 
                           n' <- ppr n 
                           t0' <- ppr t0
                           return $ n' <+> PP.text "=" <+> t0') defs
      let pdefs' = punctuate PP.comma pdefs
      return $ PP.braces (hsep pdefs') <+> PP.space <+> PP.text "in" <+> PP.space <+> t'

-- Pretty printing conveniences --

pprintEqn :: Eqn -> String
pprintEqn e = render . runLFreshM . ppr $ e

pprintType :: GoType -> String
pprintType t = render . runLFreshM . ppr $ t

-------

-- Lexer --
lexer :: T.TokenParser ()

ldef = emptyDef {  T.identStart = P.letter
                 , T.identLetter = P.alphaNum
                 , T.reservedNames = [ "def"
                                     , "call"
                                     , "close"
                                     , "spawn"
                                     , "let"
                                     , "newchan"
                                     , "select"
                                     , "case"
                                     , "endselect"
                                     , "if"
                                     , "else"
                                     , "endif"
                                     , "tau"
                                     , "send"
                                     , "recv" ] }
 
lexer = T.makeTokenParser ldef

whiteSpace = T.whiteSpace lexer
reserved   = T.reserved lexer
parens     = T.parens lexer
identifier = T.identifier lexer
natural    = T.natural lexer
integer    = T.integer lexer
semi       = T.semi lexer
symbol     = T.symbol lexer

-- Parser --

data Prog = P [Def]
            deriving (Eq, Show)
                     
data Def =  D String [String] Interm
            deriving (Eq, Show)
                     
data Interm = Seq [Interm]
              | Call String [String]
              | Cl String
              | Spawn String [String]
              | NewChan String String Integer
              | If Interm Interm
              | Select [Interm]
              | T
              | S String
              | R String
              | Zero
         deriving (Eq, Show)

seqInterm :: P.Parser Interm
seqInterm = do
  list <- P.sepBy1 itparser semi
  return $ if L.length list == 1 then head list else Seq list

pparser :: P.Parser Prog
pparser = do
  l <- many dparser
  return $ P l


dparser :: P.Parser Def
dparser = do
  { reserved "def"
  ; x <- identifier
  ; list <- parens (P.sepBy1 identifier (P.char ','))
  ; symbol ":"
  ; d <- seqInterm
  ; return $ D x list d
  }


itparser :: P.Parser Interm 
itparser = 
  do { reserved  "close"
     ; c <- identifier
     ; return $ (Cl c) }
  <|>
  do { reserved "spawn"
     ; x <- identifier
     ; list <- parens (P.sepBy1 identifier (P.char ','))
     ; return $ Spawn x list }
  <|>
  do { reserved "select"
     ; l <- many (reserved "case" *> seqInterm)
     ; reserved "endselect"
     ; return $ Select l }
  <|>
  do { reserved "let"
     ; x <- identifier
     ; symbol "="
     ; reserved "newchan"
     ; t <- identifier
     ; n <- natural
     ; return $ NewChan x t n }
  <|>
  do { reserved "if"
     ; t <- seqInterm
     ; reserved "else"
     ; e <- seqInterm
     ; reserved "endif"
     ; return $ If t e }
  <|>
  do { reserved "tau"
     ; return $ T   }
  <|>
  do { reserved "send"
     ; c <- identifier
     ; return $ S c  }
  <|>
  do { reserved "recv"
     ; c <- identifier
     ; return $  R c  }
  <|>
  do  { reserved "call"
  ; c <- identifier
  ; list <- parens (P.sepBy1 identifier (P.char ','))
  ;  return $ Call c list }
 <|>
  do { return $ Zero }

mainparser :: P.Parser Prog
mainparser = whiteSpace >> pparser <* P.eof

parseprog :: String -> Either P.ParseError Prog
parseprog inp = P.parse mainparser "" inp

parseTest s =
  case parseprog s of
  Left err -> print err
  Right s -> print s
  
-------


-- Once unfoldings of GoTypes and EquationSys --

unfoldType :: GoType -> M GoType
unfoldType (Send c t) = do
  t' <- unfoldType t
  return $ Send c t'
unfoldType (Recv c t) = do
  t' <- unfoldType t
  return $ Recv c t'
  
unfoldType (Tau t) = do
  t' <- unfoldType t
  return $ Tau t'
unfoldType (IChoice t1 t2) = do
  t1' <- unfoldType t1
  t2' <- unfoldType t2
  return $ IChoice t1' t2'
unfoldType (OChoice l) = do
 lm' <- mapM unfoldType l
 return $ OChoice lm'
unfoldType (Par l) = do
 lm' <- mapM unfoldType l
 return $ Par lm'
unfoldType (New bnd) = do
  (c,t) <- unbind bnd
  t' <- unfoldType t
  -- GC if c not used
  if c `S.notMember` fv t'
    then return t'
    else return (New (bind c t'))                              
unfoldType (Null) = return Null
unfoldType (Close c t) = do
  t' <- unfoldType t
  return $ Close c t'
unfoldType (TVar x) = return $ TVar x
unfoldType (ChanInst t lc) = do  -- P(~c)
  t' <- unfoldType t
  case t' of
   ChanAbst bnd -> do -- P == (\~d.P)(~c)
     (ld,t0) <- unbind bnd
     let perm = L.foldr (\(d,c) acc -> compose acc (single (AnyName d) (AnyName c))  ) (Unbound.LocallyNameless.empty) (zip ld lc)
     return $ swaps perm t0
   otherwise -> return $ ChanInst t' lc
unfoldType (ChanAbst bnd) = do
  (c,t) <- unbind bnd
  t' <- unfoldType t
  return $ ChanAbst (bind c t')



unfoldEqn :: Eqn -> M Eqn
unfoldEqn (EqnSys bnd) = do
    (r,body) <- unbind bnd
    let vars = unrec r
    let newbody = L.foldr (\(x,Embed rhs) body -> subst x rhs body) body vars
    return $ EqnSys (bind (rec vars) newbody)

unfoldTop :: Eqn -> M Eqn
unfoldTop (EqnSys bnd) = do
    (r,body) <- unbind bnd
    let vars = unrec r
    let newbody = L.foldr (\(x,Embed rhs) body -> subst x rhs body) body vars
    bla <- unfoldType newbody
    return $ EqnSys (bind (rec vars) bla)



---- Testing Area: Please stand back -----
simpleEx =  eqn "t" "c" (Send (s2n "c") (new "d" (chanInst "t" "d"))) (chanInst "t" "c")




twored = do
  t <- unfoldTop simpleEx
  unfoldTop t

twored' = do
  t <- twored
  return $ pprintEqn t

-- -- Testing stuff --

--eqnl :: [(String,[String],GoType)] -> GoType -> Eqn
--eqnl l t = EqnSys (bind (rec (map (\(s,c,t1) -> (string2Name s ,Embed(bind (map string2Name c) t1) )) l)) t)

--testSubst = tvar "s" "c"

-- test1 = eqn "t" "c" (Send (namify "c") (tvar "t" "c")) (new "c" (tvar "t" "c"))

-- -- Testing re-use of a in eq s. Should be free [OK]
-- test2 = eqnl [("t",["a"] , (Send (namify "a") (tvar "t" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "a") (tvar "s" "b"))  ) ] (new "c" (Par (tvar "t" "c") (tvar "s" "c")))

-- -- Baseline for recursive stuff [OK]
-- test3 = eqnl [("t",["a"] , (Send (namify "a") (tvar "t" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) ] (new "c" (Par (tvar "t" "c") (tvar "s" "c")))

-- -- Testing mutually recursive binders [OK]
-- test4 = eqnl [("t",["a"] , (Send (namify "a") (tvar "s" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "t" "b"))  ) ] (new "c" (Par (tvar "t" "c") (tvar "s" "c")))

-- -- Testing for free "a" in main [OK]
-- test5 = eqnl [("t",["a"] , (Send (namify "a") (tvar "t" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) ] (new "c" (Par (tvar "t" "a") (tvar "s" "c")))

-- -- Testing for free rec var in main [OK]
-- test6 = eqnl [("t",["a"] , (Send (namify "a") (tvar "t" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) ] (new "c" (Par (tvar "d" "a") (tvar "s" "c")))

-- -- All should be aeq to test3 [OK All]
-- test3aeq1 = eqnl [("t",["a"] , (Send (namify "a") (tvar "t" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) ] (new "d" (Par (tvar "t" "d") (tvar "s" "d")))

-- test3aeq2 = eqnl [("xpto",["a"] , (Send (namify "a") (tvar "xpto" "a")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) ] (new "d" (Par (tvar "xpto" "d") (tvar "s" "d")))

-- test3aeq3 = eqnl [("t",["b"] , (Send (namify "b") (tvar "t" "b")) ) , 
--               ("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) ] (new "d" (Par (tvar "t" "d") (tvar "s" "d")))

-- -- Won't be
-- test3aeq4 = eqnl [("s" ,["b"] ,(Recv (namify "b") (tvar "s" "b"))  ) , 
--               ("t",["a"] , (Send (namify "a") (tvar "t" "a")) ) ] (new "c" (Par (tvar "t" "c") (tvar "s" "c")))

-- Unfolding Test --


--(Bind (Rec [(Name GoType, Embed (Bind [Name String] GoType))]) GoType)



assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

--eqn :: String -> GoType -> GoType -> Eqn
--eqn s t1 t2 = EqnSys (bind (rec (string2Name s , Embed(t1) )) t2)


--eqnSys :: [(String,GoType)] -> GoType -> Eqn
--eqnSys l t2 = EqnSys (bind (rec ( map (\(s,t1) -> (string2Name s, Embed(t1))) l  )) t2)



