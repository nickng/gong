{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
           , DeriveGeneric, DeriveAnyClass
  #-}

module GoTypes where

import Unbound.LocallyNameless hiding (Generic)

import Control.Applicative
import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Trans.Maybe
import Data.List as L
import Data.Set (Set)
import qualified Data.Set as S
import Data.Maybe

import GHC.Generics (Generic)
import Control.DeepSeq


-- DEBUG
import System.IO.Unsafe
import Debug.Trace

data Channel

type ChName = Name Channel


type EqnName = Name GoType


data GoType = Send ChName GoType
            | Recv ChName GoType
            | Tau GoType
            | IChoice GoType GoType -- Just two things?
            | OChoice [GoType]
            | Par [GoType]
            | New Int (Bind ChName GoType)
            | Null
            | Close ChName GoType
            | TVar EqnName
            | ChanInst GoType [ChName] -- P(c)
            | ChanAbst (Bind [ChName] GoType) -- \c.P
            | Seq [GoType]
            | Buffer ChName (Bool, Int, Int) -- True when Open, Bound, Current
            | ClosedBuffer ChName -- Only used for guard/label
    deriving (Show)


isBuffer :: GoType -> Bool
isBuffer (Buffer _ _) = True
isBuffer _ = False

data Eqn = EqnSys (Bind (Rec [(EqnName , Embed GoType)]) GoType)
    deriving (Show)
-- inner Proc will always be ChanAbst
             
$(derive [''Channel,''GoType,''Eqn])

--instance Alpha Channel
instance Alpha GoType
instance Alpha Eqn


-- -- PARALLEL STUFF
-- instance NFData GoType where rnf x = seq x ()
-- instance NFData Eqn where rnf x = seq x ()
-- instance NFData (Name a) where rnf x = seq x ()

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

new :: Int -> String -> GoType -> GoType
new i s t = New i $ bind (s2n s) t

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
                        Par l -> case (flattenPar x) of
                                    Par l' -> l'++(flattenPar' xs)
                                    t -> t:(flattenPar' xs)
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
gcBNames' (New i bnd) = do
  (c,t) <- unbind bnd
  t' <- gcBNames' t
  -- GC if c not used
  if c `S.notMember` fv t' 
    then return t'
    else return (New i (bind c t'))                              
gcBNames' (Null) = return Null
gcBNames' buf@(Buffer c _) = return buf  
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
gcBNames' (Seq l) = do
  l' <- mapM gcBNames' l
  return $ Seq l'
  

gcBNames :: GoType -> GoType
gcBNames = runFreshM . gcBNames'







-- Open top-level bound names in a list of parallel types --
-- return is a list of (mc,t) where mc is Nothing if t is
-- closed and Just(c) otherwise.
openBNames :: [GoType] -> M [([Maybe (Int, ChName)],GoType)]
openBNames (x:xs) = do
     (l,t) <- openBNamesT x 
     rest <- openBNames xs
     return $ (l,t):rest    
openBNames [] = return $ [([Nothing],Null)]

openBNamesT :: GoType -> M ([Maybe (Int, ChName)], GoType)
openBNamesT (New i bnd) = do
            (c,t) <- unbind bnd
            (l,t') <- openBNamesT t
            return $ ( Just(i,c):l , t')
openBNamesT t = return $ ([Nothing],t)
    

-- Reconstructs the appropriate GoType from calls
-- to openBNames
closeBNames ::  M [([Maybe (Int, ChName)],GoType)] -> M GoType
closeBNames m  = do
  l <- m
  let (names,ts) = unzip l
  let names' = concat names
  return $ L.foldr (\mc end ->
                    case mc of
                      Just(i,c) -> New i (bind c end)
                      Nothing -> end) (Par ts) names'

-- Composes open/close and escapes the freshness monad --
pullBNamesPar :: GoType -> GoType
pullBNamesPar (Par l) =
  runFreshM (closeBNames . openBNames $ l)
pullBNamesPar t = t 

  
nf :: M GoType -> M GoType
nf t = do t1 <- t
          (nf' (gcBNames t1))
   where nf' Null = return Null
         nf' (Send c t) = do
             t' <- nf' t
             return $ (Send c t')
         nf' (Recv c t) = do
             t' <- nf' t
             return $ (Recv c t')
         nf' (Tau t) = do
             t' <- nf' t
             return $ (Tau t')
         nf' (IChoice t1 t2) = do       
             t1' <- nf' t1
             t2' <- nf' t2
             return $ IChoice t1' t2'
         nf' (OChoice l) = do
             l' <- mapM nf' l
             return $ OChoice l'
         nf' t@(Par l) = do
             let t' = (gcNull . pullBNamesPar  . flattenPar $ t)
             case t' of
              Par l' -> do 
                          l'' <- mapM nf' l'
                          return $ Par l''
              _ -> nf' t'
         nf' (New i bnd) = do
             (c,t) <- unbind bnd
             t' <- nf' t
             return $ (New i (bind c t'))
         nf' (Close c t) = do
             t' <- nf' t
             return $ (Close c t')
         nf' (TVar x) = return $ TVar x
         nf' t@(ChanInst t0 l) = return $ t
         nf' (ChanAbst bnd) = do
             (l,t) <- unbind bnd
             t' <- nf' t
             return $ (ChanAbst (bind l t'))
         nf' (Seq l) = do
             l' <- mapM nf' l
             return $ Seq l'
         nf' buf@(Buffer c _) = return buf
             

-- structCong :: GoType -> GoType -> Bool
-- structCong t1 t2 = (nf t1) `aeq` (nf t2)


-----------


gcBufferList :: [ChName] -> [GoType] -> [GoType] -> [GoType]
gcBufferList names prev [] = prev
gcBufferList names prev (x:xs) = case x of
  Null -> gcBufferList names prev xs
  Buffer c (o,i,j) ->
    if (j == 0) || (c `L.elem` names) || (not o)
    then let fna ys = L.foldr (++) [] $ L.map fv ys
             left = fna prev
             right = fna xs
         in if (c `L.elem` (right++left)) || ((L.null prev) && (L.null xs))
            then gcBufferList names (prev++[x]) xs
            else gcBufferList names prev xs
    else gcBufferList names (prev++[x]) xs
  otherwise -> gcBufferList names (prev++[x]) xs
                              
gcBuffer :: M GoType -> M GoType
gcBuffer t = do t' <- t
                gcBuffer' [] t'

gcBuffer' :: [ChName] -> GoType -> M GoType
gcBuffer' names (Par list) = return $ Par $ gcBufferList names [] list
gcBuffer' names (New i bnd) = do
  (c,t) <- unbind bnd
  t' <- gcBuffer' (c:names) t
  return $ New i (bind c t')
gcBuffer' names t = return t

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
unfoldType (New i bnd) = do
  (c,t) <- unbind bnd
  t' <- unfoldType t
  -- GC if c not used
  if c `S.notMember` fv t'
    then return t'
    else return (New i (bind c t'))                              
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
     let perm = L.foldr (\(d,c) acc -> compose acc (single (AnyName d) (AnyName c))  )
                (Unbound.LocallyNameless.empty) (zip ld lc)
     return $ swaps perm t0
   otherwise -> return $ ChanInst t' lc
unfoldType (ChanAbst bnd) = do
  (c,t) <- unbind bnd
  t' <- unfoldType t
  return $ ChanAbst (bind c t')
unfoldType (Seq l) = do
  l' <- mapM unfoldType l
  return $ Seq l'


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


---- Fencing predicate for types ----

-- G ; ~y ; ~z |-t T  
-- G records previously encountered recursive calls
-- ~y represents names that t can use if T is single-threaded
-- ~z represents names that a sub-process of T can use if T is multi-threaded


-- EqnSys (Bind (Rec [(EqnName , Embed GoType)]) GoType)

finMem :: (Eq a) => [a] -> [a] -> Bool
finMem l1 l2 = not (null l1 || null l2 || (length l1 /= length l2)) &&
                 let sl1 = tail (inits l1) in 
                    aux sl1 l2 l1                    
   where aux (x:y:xs) l l1 = if (L.isSuffixOf x l) then
                             null ((drop (length x) l1) `intersect` l)
                          else
                             aux (y:xs) l l1
         aux [x] l l1 = null (x `intersect` l)
         aux [] l l1 = False

-- abd `finMem` abc = True
-- abc `finMem` abc = False
-- bcda  `finMem` abcd = False
-- cdab `finMem` abcd = False
-- cdaa `finMem` abcd = False               

checkFinite :: Bool -> [(EqnName , Embed GoType)] -> (Set EqnName) ->
                 [ChName] -> [ChName] ->  EqnName -> GoType -> M Bool
checkFinite debug defEnv pRecs ys zs cDef (Send c t) = checkFinite debug defEnv pRecs ys zs cDef t
checkFinite debug defEnv pRecs ys zs cDef (Recv c t) = checkFinite debug defEnv pRecs ys zs cDef t
checkFinite debug defEnv pRecs ys zs cDef (Tau t)    = checkFinite debug defEnv pRecs ys zs cDef t
checkFinite debug defEnv pRecs ys zs cDef (IChoice t1 t2) = do
                             b1 <- checkFinite debug defEnv pRecs ys zs cDef t1
                             b2 <- checkFinite debug defEnv pRecs ys zs cDef t2
                             return $ b1 && b2
checkFinite debug defEnv pRecs ys zs cDef (OChoice l) = do
                             foldM (\acc t -> do
                                               b <- checkFinite debug defEnv pRecs ys zs cDef t
                                               return $ b && acc) True l
checkFinite debug defEnv pRecs ys zs cDef (Par [t]) = checkFinite debug defEnv pRecs ys zs cDef t
checkFinite debug defEnv pRecs ys zs cDef (Par l) = do
                             foldM (\acc t -> do
                                               b <- checkFinite debug defEnv pRecs [] (zs++ys) cDef t
                                               return $ b && acc) True l  
checkFinite debug defEnv pRecs ys zs cDef (New i bnd) = do
                              (c,t) <- unbind bnd
                              checkFinite debug defEnv pRecs ys zs cDef t
checkFinite debug defEnv pRecs ys zs cDef (Null) = return $ True
checkFinite debug defEnv pRecs ys zs cDef (Close c t) = checkFinite debug defEnv pRecs ys zs cDef t
checkFinite debug defEnv pRecs ys zs cDef t@(TVar x) = error $ "[checkFinite] Oops: "++(show t)
                                                 -- Should be handled in ChanInst
checkFinite debug defEnv pRecs ys zs cDef (ChanInst (TVar x) l) =
               if (x == cDef) then
                 -- return $ ((not . null $ ys) || (l `finMem` zs))
                 if ((not . null $ ys) || (l `finMem` zs))
                 then return True
                 else if debug
                      then error $ "Not fenced: "++(show ((l,zs),ys))
                      else return False
               else
                  if (x `S.member` pRecs) then
                   return $ True 
                  else
                    do
                      let tdef = (case (L.lookup x defEnv) of
                                   Just(Embed(t)) -> t
                                   _ -> error $ "Something went wrong, can't find: "++(show x)) 
                      let tabs = (case tdef of
                                   ChanAbst bnd -> bnd
                                   _ -> error "boom! wtf")
                      (params,abs) <- unbind tabs
                      let perm = L.foldr (\(d,c) acc -> compose acc (single (AnyName d) (AnyName c))  )
                                              (Unbound.LocallyNameless.empty) (zip params l)
                      checkFinite debug defEnv (S.insert x pRecs) ys zs cDef (swaps perm abs)
checkFinite debug defEnv pRecs ys zs cDef (ChanAbst bnd) = return $ True -- this shouldn't come up here I think
checkFinite debug defEnv pRecs ys zs cDef (Seq l) = do
                               foldM (\acc t -> do
                                               b <- checkFinite debug defEnv pRecs ys zs cDef t
                                               return $ b && acc) True l


-- maybe just check main?
checkFiniteP debug (EqnSys bnd) = do
             (defs,main) <- unbind bnd
             let defEnv = unrec defs
             b <- foldM (\acc (x,Embed(ChanAbst bnd))  -> do
                              (l,t) <- unbind bnd
                              b <- if null l then return True else checkFinite debug defEnv (S.empty) l [] x t
                              return $ (acc && b)) True defEnv
             b' <- checkFinite debug defEnv (S.empty) [] [] (s2n "main") main
             return $ (b && b')

runCheck :: Bool -> Eqn -> Bool
runCheck debug p = runFreshM $ checkFiniteP debug p

