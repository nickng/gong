{-# LANGUAGE MultiParamTypeClasses
           , TemplateHaskell
           , ScopedTypeVariables
           , FlexibleInstances
           , FlexibleContexts
           , UndecidableInstances
  #-}


module PrettyGoTypes where


import Unbound.LocallyNameless
import Control.Applicative
import Control.Arrow ((+++))
import Control.Monad
import Control.Monad.Trans.Maybe
import Data.List as L
import Data.Set as S
import Data.Maybe

import qualified Text.PrettyPrint as PP
import Text.PrettyPrint (render,(<+>),hsep,punctuate,brackets,(<>),text,Doc)


import GoTypes

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
   let prettyl = punctuate (PP.space <> PP.text "|") l'
   return $ (hsep prettyl)
  ppr (New i bnd) = lunbind bnd $ \(c,t) -> do
      c' <- ppr c
      t' <- ppr t
      return $ PP.text "new" <+> (PP.int i) <+> c' <> dot <> (PP.parens t')
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
  ppr (Seq l) = do
    l' <- mapM ppr l
    let plist = punctuate PP.semi l'
    return $ hsep plist
  ppr (Buffer c (open,i,j)) = do
    c' <-  ppr c
    if open
      then return $ PP.text "[" <> c' <> PP.text  ":"
           <>  PP.text "B:" <> (PP.int i)
           <>  PP.text "K:" <> (PP.int j) <> PP.text "]"
      else return $ PP.text "(" <> c' <> PP.text  ":"
           <>  PP.text "B:" <> (PP.int i)
           <>  PP.text "K:" <> (PP.int j) <> PP.text ")"
      
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

pprintTypeList :: [GoType] -> String
pprintTypeList xs = L.foldr (\x -> \y -> x++"\n"++y) [] $ L.map pprintType xs

-------
