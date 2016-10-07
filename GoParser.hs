

module GoParser where

import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Trans.Maybe
import Data.Functor
import Data.List as L
import Data.Set as S
import Data.Maybe
import Control.Applicative ((<*),(*>))
import Unbound.LocallyNameless

import qualified Text.ParserCombinators.Parsec as P
import Text.ParserCombinators.Parsec ((<|>),many)
import qualified Text.ParserCombinators.Parsec.Token as T
import Text.ParserCombinators.Parsec.Language

import qualified GoTypes as GT
import qualified PrettyGoTypes as PP
-- Types --

data Prog a = P [Def a]
            deriving (Eq, Show)
                     
data Def a =  D String [String] a
            deriving (Eq, Show)

instance Functor Def where
    fmap f (D s l p) = D s l (f p)

instance Functor Prog where
    fmap f (P l) = P (fmap (fmap f) l)
                     
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

-- Assumptions currently being exploited by Translation to GoTypes:
-- (1) If and Select have no real continuation
-- (2) Parser always terminates every control flow branch with
--     a Zero


-- The flow from text to GoTypes/Eqn is:
-- (1) Parse via pparser
-- (2) Eliminate trailing zeros in If/Select/Call
-- (3) Transform into GoTypes/Eqn (with Seq only for non-prefix)


type ProgGo = Prog Interm
type DefGo = Def Interm



-- Lexer --
lexer :: T.TokenParser ()

ldef = emptyDef {  T.identStart = P.letter
                 , T.identLetter = (P.alphaNum <|> P.char '_' <|> P.char '.' 
                                               <|> P.char '$'<|> P.char '#')
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
                                     , "recv" ]
                 , T.commentLine = "--"
                 }
 
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

seqInterm :: P.Parser Interm
seqInterm = do
  list <- P.sepBy1 itparser semi
  return $ if L.length list == 1 then head list else Seq list

pparser :: P.Parser (ProgGo)
pparser = do
  l <- many dparser
  return $ P l


dparser :: P.Parser (DefGo)
dparser = do
  { reserved "def"
  ; x <- identifier
  ; list <- parens (P.sepBy identifier (P.char ',' <* P.spaces))
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
     ; list <- parens (P.sepBy identifier (P.char ',' <* P.spaces))
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
     ; symbol ","
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
  ; list <- parens (P.sepBy identifier (P.char ',' <* P.spaces))
  ;  return $ Call c list }
 <|>
  do { return $ Zero }

mainparser :: P.Parser (ProgGo)
mainparser = whiteSpace >> pparser <* P.eof


parseprog :: String -> Either P.ParseError (ProgGo)
parseprog inp = P.parse mainparser "" inp

parseTest s =
  case parseprog s of
  Left err -> print err
  Right s -> print s


-------- Intermediate representation to GoTypes -------

  
-- Getting rid of Call;0, Select;0 and If;0 --

contzElim :: Interm -> Interm
contzElim (Seq l) = Seq (contzElim' l)
contzElim (If p1 p2) = If (contzElim p1) (contzElim p2)
contzElim (Select l) = Select (L.map contzElim l)
contzElim p = p

contzElim' (x:y:xs) = case (x,y) of
                        (Call _ _ , Zero) -> [x] -- No need to keep going
                        (If p1 p2, Zero) -> [If (contzElim p1) (contzElim p2)]
                        (Select l , Zero) -> [Select (L.map contzElim l)]
                        (_,_) -> (contzElim x):(contzElim' (y:xs))
contzElim' ([x]) = [contzElim x]
contzElim' [] = []


contzElimProg :: ProgGo -> ProgGo
contzElimProg = fmap contzElim 



--- Transforming processed Prog into Eqn/GoTypes ---


transform :: [String] -> Interm -> GT.GoType
transform vars (Seq l) = transformSeq vars l
transform vars t = transform vars (Seq [t])



throwError :: [String] -> [String] -> GT.GoType ->  GT.GoType
throwError current known ty =
  if and $ L.map (\x -> x `elem` known) current
  then ty
  else error $ "Some of "++(show current)++" are not declared."

transformSeq :: [String] -> [Interm] -> GT.GoType
transformSeq vars (x:xs) =
  case x of
    (Call s l) -> throwError l vars $
                  GT.Seq [(GT.ChanInst (GT.TVar (s2n s)) (L.map s2n l)), (transformSeq vars xs) ]
    
    (Cl s) -> throwError [s] vars $
              GT.Close (s2n s) (transformSeq vars xs)
    
    (Spawn s l) -> throwError l vars $
                   GT.Par [(GT.ChanInst (GT.TVar (s2n s)) (L.map s2n l)) , (transformSeq vars xs)]

    (NewChan s1 s2 n) -> GT.New (fromIntegral n) (bind (s2n s1) (transformSeq (s1:vars) xs))
    
    (If p1 p2) -> GT.IChoice (transform vars p1) (transform vars p2)
    
    (Select l) -> GT.OChoice (L.map (transform vars) l)
    
    (T) -> GT.Tau (transformSeq vars xs)
    
    (S s) -> throwError [s] vars $
             GT.Send (s2n s) (transformSeq vars xs)
           
    (R s) -> throwError [s] vars $
             GT.Recv (s2n s) (transformSeq vars xs)
    (Zero) -> GT.Null  
transformSeq vars [] = GT.Null

transformDef (D s l p) = (s2n s , Embed(GT.ChanAbst (bind (L.map s2n l) (transform l p))))
transformMain (D _ vars p) = transform vars p

transformProg :: ProgGo -> GT.Eqn
transformProg (P l) =  let main = head l
                           defs = tail l
                       in GT.EqnSys (bind (rec (L.map transformDef defs)) (transformMain main))


fullPass :: String -> Either P.ParseError (GT.Eqn)
fullPass s = case (parseprog s) of
              Left err -> Left err
              Right p -> Right (transformProg . contzElimProg $ p)

passTest :: String -> GT.Eqn
passTest s = case (fullPass s) of
              Right e -> e
              Left err -> error "Failed to parse"

---- Testing Area ----
                          
assert :: String -> Bool -> IO ()
assert s True  = return ()
assert s False = print ("Assertion " ++ s ++ " failed")

testerFile :: String -> IO ()
testerFile s = do
  f <- readFile s
  print ("Attempting to Parse: " ++ f)
  let e = passTest f
  putStr "Succeeded: "
  print . PP.pprintEqn $ e
  
testerStr :: String -> IO ()
testerStr s = do
  print ("Attempting to Parse: " ++ s)
  let e = passTest s
  putStr "Succeeded: "
  print . PP.pprintEqn $ e

p1 = "def t0() : tau ; call t0 () ; def t1(a) : send a ; call t1(a) ; def t2(b) : recv a ; call t2 (b) ;"
p2 = "def t0() : spawn t1(a) ; spawn t2(a) ; def t1(a) : send a ; call t1(a) ; def t2(b) : recv b ; call t2 (b) ;"
p3 = "def t0() : let a = newchan xpto , 0 ; spawn t1(a) ; spawn t2(a) ; def t1(a) : send a ; call t1(a) ; def t2(b) : recv a ; call t2 (b);"
p4 = "def main() : let a = newchan xpto, 0 ; spawn r(a) ; call t(a) ; def t(b) : recv b ;"

test :: IO ()
test = 
  mapM_ testerStr [p1,p2,p3,p4]
  

