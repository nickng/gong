module TypeSize where


import GoTypes
import PrettyGoTypes (pprintEqn, pprintType)
import Utils

import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

import Data.List as L
-- import Data.Set as S (intersection, null)

-- DEBUG
import System.IO.Unsafe
import Debug.Trace

type Environment = [(EqnName , Embed GoType)]

symsemBound :: [EqnName] -> Environment -> GoType -> Int
symsemBound seen defEnv (Send _ ty) = symsemBound seen defEnv ty
symsemBound seen defEnv (Recv _ ty) = symsemBound seen defEnv ty
symsemBound seen defEnv (Tau ty) = symsemBound seen defEnv ty
symsemBound seen defEnv (IChoice ty1 ty2) =
  maximum [symsemBound seen defEnv ty1, symsemBound seen defEnv ty2]
symsemBound seen defEnv (OChoice xs) = maximum (map (symsemBound seen defEnv) xs)
symsemBound seen defEnv (Par xs) = maximum (map (symsemBound seen defEnv) xs)
symsemBound seen defEnv (New i bnd) = let (c,ty) = unsafeUnbind bnd
                        in 1 + symsemBound seen defEnv ty
symsemBound seen defEnv (Null) = 0
symsemBound seen defEnv (Close _ ty) = symsemBound seen defEnv ty
symsemBound seen defEnv (ChanInst (TVar t) xs)
  | t `L.elem` seen = 0
  | otherwise =
    case L.lookup t defEnv of
      Just (Embed ty) -> symsemBound (t:seen) defEnv ty
      _ -> error $ "[symsemBound]Definition "++(show t)++" not found."
symsemBound seen defEnv (ChanAbst bnd) =  let (c,ty) = unsafeUnbind bnd
                              in symsemBound seen defEnv ty
symsemBound seen defEnv (Seq xs) = sum (map (symsemBound seen defEnv) xs)
symsemBound seen defEnv (TVar eqs) = error "[symsemBound]TVAR"




sizeOfT :: [EqnName] -> Environment -> GoType -> Int
sizeOfT seen defEnv (Send _ ty) =  1 + (sizeOfT seen defEnv ty)
sizeOfT seen defEnv (Recv _ ty) = 1 + (sizeOfT seen defEnv ty)
sizeOfT seen defEnv (Tau ty) = sizeOfT seen defEnv ty
sizeOfT seen defEnv (IChoice ty1 ty2) =
  maximum [sizeOfT seen defEnv ty1, sizeOfT seen defEnv ty2]
sizeOfT seen defEnv (OChoice xs) = maximum (map (sizeOfT seen defEnv) xs)
sizeOfT seen defEnv (Par xs) = L.foldr (+) 0 (map (sizeOfT seen defEnv) xs)
sizeOfT seen defEnv (New i bnd) = let (c,ty) = unsafeUnbind bnd
                        in  sizeOfT seen defEnv ty
sizeOfT seen defEnv (Null) = 0
sizeOfT seen defEnv (Close _ ty) = sizeOfT seen defEnv ty
sizeOfT seen defEnv (ChanInst (TVar t) xs)
  | t `L.elem` seen = 0
  | otherwise =
    case L.lookup t defEnv of
      Just (Embed ty) -> sizeOfT (t:seen) defEnv ty
      _ -> error $ "[sizeOfT]Definition "++(show t)++" not found."
sizeOfT seen defEnv (ChanAbst bnd) =  let (c,ty) = unsafeUnbind bnd
                              in sizeOfT seen defEnv ty
sizeOfT seen defEnv (Seq xs) = sum (map (sizeOfT seen defEnv) xs)
sizeOfT seen defEnv (TVar eqs) = error "[sizeOfT]TVAR"


isRecPar :: [EqnName] -> Environment -> GoType -> Int
isRecPar seen defEnv (Send _ ty) = isRecPar seen defEnv ty
isRecPar seen defEnv (Recv _ ty) = isRecPar seen defEnv ty
isRecPar seen defEnv (Tau ty) = isRecPar seen defEnv ty
isRecPar seen defEnv (IChoice ty1 ty2) =
  maximum [isRecPar seen defEnv ty1, isRecPar seen defEnv ty2]
isRecPar seen defEnv (OChoice xs) = maximum (map (isRecPar seen defEnv) xs)

isRecPar seen defEnv (Par xs) =
  let (recs, notrecs) = partition (\x -> not $ L.null $ intersect seen (fvTyp x)) xs
      sizes = L.map (sizeOfT [] defEnv) notrecs
  in if L.null recs
     then 0
     else maximum (0:sizes)
isRecPar seen defEnv (New i bnd) = let (c,ty) = unsafeUnbind bnd
                        in isRecPar seen defEnv ty
isRecPar seen defEnv (Null) = 0
isRecPar seen defEnv (Close _ ty) = isRecPar seen defEnv ty
isRecPar seen defEnv (ChanInst (TVar t) xs)
  | t `L.elem` seen = 0
  | otherwise =
    case L.lookup t defEnv of
      Just (Embed ty) -> isRecPar (t:seen) defEnv ty
      _ -> error $ "[isRecPar]Definition "++(show t)++" not found."
isRecPar seen defEnv (ChanAbst bnd) =  let (c,ty) = unsafeUnbind bnd
                              in isRecPar seen defEnv ty
isRecPar seen defEnv (Seq xs) = sum (map (isRecPar seen defEnv) xs)
isRecPar seen defEnv (TVar eqs) = error "[isRecPar]TVAR"


maxnestednames :: Eqn -> Int
maxnestednames (EqnSys bnd) = let (defs,main) = unsafeUnbind bnd
                              in symsemBound [] (unrec defs) main

sizeOfEqs :: Eqn -> Int
sizeOfEqs (EqnSys bnd) =
  let (defs,main) = unsafeUnbind bnd
      deflist = unrec defs
      fun (n,(Embed (ChanAbst bnd))) = let (l,t) = unsafeUnbind bnd
                                       in isRecPar [n] (unrec defs) t
  in maximum (0:(L.map fun deflist))
