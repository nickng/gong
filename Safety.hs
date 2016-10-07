module Safety where

import Liveness
import GoTypes
import SymbolicSem
import Utils
import PrettyGoTypes

import Unbound.LocallyNameless
import Unbound.LocallyNameless.Ops

import Data.List as L
import Data.Set as S (intersection, null, fromList)

-- DEBUG
import System.IO.Unsafe
import Debug.Trace




getContinuation :: GoType -> Maybe [GoType]
getContinuation (Close c ty) = Just [ty, Buffer c (False, 0,0)] -- DEAL WITH BUFFER
getContinuation _ = Nothing

closebarbs :: GoType -> [GoType]
closebarbs (Close c ty) = [Close c Null]
closebarbs t = []

forbiddenAction :: GoType -> [GoType]
forbiddenAction (Send n t) = [Send n Null]
forbiddenAction (Close c ty) = [Close c Null]
forbiddenAction (New i bnd) = let (c,ty) = unsafeUnbind bnd
                              in forbiddenAction ty
forbiddenAction (Par xs) = L.foldr (++) [] $ L.map forbiddenAction xs
forbiddenAction t = []


badmatch :: GoType -> GoType -> Bool
badmatch (Close c ty) (Send n t) = c == n
badmatch (Close c ty) (Close n t) = c == n
badmatch _ _ = False


noclose :: [GoType] -> [GoType] -> Bool
noclose [] [] = True
noclose list@(x:xs) ys =
  let prod = cartProd list ys
  in L.null $ L.filter (\(x,y) -> badmatch x y) prod


checkPair :: GoType -> GoType -> Bool
checkPair t1 t2 = noclose (closebarbs t1) (forbiddenAction t2)


checkList :: GoType -> [GoType] -> Bool
checkList _ [] = True
checkList current (x:xs) = if (checkPair current x)
                           then (checkList current xs)
                           else False -- error $ "Term no safe: "++(pprintType x)
                           
                           


-- Given a parallel composition of type, check whether each
-- one can make a move
--
checkAllSuccs :: [ChName] -> Int -> Rec [(EqnName, Embed GoType)] -> [GoType] -> [GoType] -> M Bool
checkAllSuccs names k sys prev [] = return True
checkAllSuccs names k sys prev (x:next) =
  case getContinuation x of
    Just ty -> 
      do  let temp = succsNode k names (EqnSys $ bind sys (Par (prev++ty++next))) :: M [Eqn]
          nexts <- temp
          gotypes <- eqnToTypes temp
          rest <- (checkAllSuccs names k sys (prev++[x]) next)
          return $ (checkList x gotypes) && rest
    Nothing ->  checkAllSuccs names k sys (prev++[x]) next





safety :: Bool -> Int -> M [Eqn] -> M Bool
safety debug k eqs =
  do list <- eqs
     case list of
       (sys@(EqnSys bnd):xs) ->
         do (defs, main) <- unbind bnd
            ty <- extractType (return main)
            let names = L.nub $ fv ty
            out <- checkAllSuccs names k defs [] ty
            if out
              then safety debug k $ return xs
              else if debug
                   then error $ "Term not safe: " ++(show $ L.map pprintType ty)
                   else return False
       [] -> return True
