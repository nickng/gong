{-# LANGUAGE BangPatterns #-}
module Liveness where

import GoTypes
import SymbolicSem
import Utils
import PrettyGoTypes


import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

import Control.Parallel.Strategies
import Data.List as L
import Data.Set as S (intersection, null, fromList, toList)

-- import Control.Monad.Trans.State.Lazy
-- import Control.Monad
-- import Control.Concurrent.Async

-- DEBUG
import System.IO.Unsafe
import Debug.Trace


-- Barbs of a "sequential" type
barbs :: GoType -> [GoType]
barbs (Send n t) = [Send n Null]
barbs (Recv n t) = [Recv n Null]
barbs (OChoice xs) = L.foldr (++) [] $ L.map barbs xs
barbs (New i bnd) = let (c,ty) = unsafeUnbind bnd
                    in barbs ty
barbs (Par xs) = L.foldr (++) [] $ L.map barbs xs
barbs (Buffer c (open,b,k))
  | (k < b) && (k > 0) = [Send c Null, Recv c Null]
  | k > 0 = [Send c Null]
  | k < b = [Recv c Null]
  | not open = [Send c Null]
  | otherwise = [] 
barbs t = []


synchronise :: [GoType] -> [GoType] -> Bool
synchronise [] _ = True -- No barbs: always good
synchronise [g] xs = not $ L.null $ L.filter (\x -> match x g) xs
synchronise list@(x:y:xs) ys =
  let prod = cartProd list ys
  in not $ L.null $ L.filter (\(x,y) -> match x y) prod


matchTypes :: GoType -> GoType -> Bool
matchTypes current candidate =
  synchronise (barbs current) (barbs candidate)

findMatch :: GoType -> [GoType] -> Bool
findMatch _ [] = False
findMatch current (x:xs) = (matchTypes current x)
                           ||
                           (findMatch current xs)
                           

eqnToTypes :: M [Eqn] -> M [GoType]
eqnToTypes mlist = do list <- mlist
                      helper list
  where helper :: [Eqn] -> M [GoType]
        helper ((EqnSys x):xs) = do (d,t) <- unbind x
                                    rest <- helper xs
                                    return $ (t:rest)
        helper [] = return []

-- Given a parallel composition of type, check whether each
-- one can make a move
--
checkStates :: [ChName] -> Int -> Rec [(EqnName, Embed GoType)] -> [GoType] -> [GoType] -> M Bool
checkStates names k sys prev [] = return True
checkStates names k sys prev (x:next) =
  if isBuffer x
  then checkStates names k sys (prev++[x]) next
  else
    do  let temp = succsNode k names (EqnSys $ bind sys (Par (prev++next))) :: M [Eqn]
        nexts <- temp
        gotypes <- eqnToTypes temp
        rest <- (checkStates names k sys (prev++[x]) next)
        return $
          (
           -- if
            (findMatch x gotypes)
            -- then True
            -- else error $ show (pprintType x ,L.map pprintType gotypes)
          )
          && rest


liveness :: Bool -> Int -> M [Eqn] -> M Bool
liveness debug k eqs =
  do list <- eqs
     case list of
       (sys@(EqnSys bnd):xs) ->
         do (defs, main) <- unbind bnd
            ty <- -- trace (show (defs,main)) $
                  extractType (return main)
            let names = L.nub $ fv ty :: [ChName]
            out <- checkStates names k defs [] ty
            if out
              then liveness debug k $ return xs
              else if debug
                   then error $ "Term not live: " ++(show $ L.map pprintType ty)
                   else return False
       [] -> return True




-- ATTEMPT AT PARALLELISATION OF LIVENESS
--
atomLiveness :: Int -> Eqn -> Bool
atomLiveness k eq = runFreshM $ helper k eq
  where helper k eq =
          case eq of
            sys@(EqnSys bnd) ->
              do (defs, main) <-unbind bnd
                 ty <- -- trace (show (defs,main)) $
                       extractType (return main)
                 let names = L.nub $ fv ty
                 checkStates names k defs [] ty



mapLiveness :: Int -> [Eqn] -> Bool
mapLiveness k eqs = helper
  where helper =
            let list = map (atomLiveness k) eqs `using` parListChunk ((length eqs) `div` 8) rpar
            in L.and list
       
-- atomLiveness :: Int -> Eqn -> M Bool
-- atomLiveness k eq = helper k eq
--   where helper k eq =
--           case eq of
--             sys@(EqnSys bnd) ->
--               do (!defs, main) <- unbind bnd
--                  ty <- trace (show main) $ extractType (return main)
--                  let names = L.nub $ fv ty :: [ChName]
--                  checkStates names k defs [] ty



-- -- mkStrat :: Strategy a -> Strategy m [a]

-- mapLiveness :: Int -> M [Eqn] -> M Bool
-- mapLiveness k eqs' = helper
--   where helper = do eqs <- eqs'
--                     let list = (mapM (atomLiveness k) eqs :: M [Bool])
--                                `using` rpar -- (parListChunk ((length eqs) `div` 8) rpar)
--                     list' <- list
--                     return $ L.and list'


-- metaLiveness :: Int -> M [Eqn] -> M Bool
-- metaLiveness k eqs' = helper
--   where helper = do eqs <- eqs'
--                     let (left,right) = splitAt ((length eqs) `div` 2) eqs
--                     t1 <- async return $ map (atomLiveness k) left
--                     t2 <- async return $ map (atomLiveness k) right
--                     w1 <- wait t1
--                     w2 <- wait t2
--                     return $ w1 && w2
