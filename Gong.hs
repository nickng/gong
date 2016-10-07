{-# LANGUAGE DeriveDataTypeable,  BangPatterns #-}

import GoParser (fullPass)
import GoTypes
import PrettyGoTypes (pprintEqn, pprintType, pprintTypeList)
import SymbolicSem
import Liveness
import Safety
import TypeSize (maxnestednames, sizeOfEqs)

import Data.List as L
import Unbound.LocallyNameless (runFreshM,unbind)

import System.Environment
import System.FilePath.Posix
import System.Process
import System.Console.CmdArgs
import Control.Monad
import System.Console.ANSI


data CheckMode = Safety
                 | Liveness
                 | All
                 | Debug
                 | List
                 | ParLive
                 deriving (Data,Typeable,Show,Eq)

data Checker = Checker
               { check :: CheckMode
               , gofile :: String
               , kbound :: Int -- NB: if set to 888, will use EXPERIMENTAL parallelisation of Liveness
               }
             deriving (Data,Typeable,Show,Eq)
                      
submodes =  enum
            [ All &= help "Check liveness and behavioural safety (default) " &= name "A"
            , Liveness  &= help "Check liveness" &= name "L"
            , Safety &= help "Check behavioural safety" &= name "S"
            , Debug  &= help "Show liveness/safety error terms (debug)" &= name "D"
            , List  &= help "Show list of k-reachable terms (debug)" &= name "N"
            ]

subargs = Checker { check = submodes
                  , gofile = def &= argPos 0 &= typ "FILE"
                  , kbound = def &= opt "-1"  &= argPos 1 &= typ "INT (optional bound)"
                  }
          &= help "Go-Types liveness and safety checks"


main :: IO ()
main = do
  pargs <- cmdArgs (modes [subargs])
  tyfile <- (readFile $ gofile pargs)
  case fullPass tyfile of
    Left err -> print err
    Right ty -> do if runCheck ((check pargs) ==  Debug) ty
                     then do
                     let bound =  if (kbound pargs) == -1 || (kbound pargs) == 888
                                  then maximum [maxnestednames ty, sizeOfEqs ty]
                                  else kbound pargs
                     let listsys = succs bound ty
                     let !tylist = runFreshM listsys
                     putStrLn $ "Bound (k): "++(show bound)
                     putStrLn $ "Number of k-states: "++(show $ length tylist)
                     when ((check pargs) ==  Debug || (check pargs)==List) $ do
                       let debugty = runFreshM $ getTypes tylist
                       putStrLn $ "\n[Debug]k-reachable states:\n"++(pprintTypeList debugty)
                     when ((check pargs) ==  Liveness || (proceed pargs)) $
                       do let live = runFreshM $ liveness ((check pargs) ==  Debug) bound listsys
                          printResult "Liveness" $ if (kbound pargs) == 888
                                                   then mapLiveness bound tylist
                                                   else live
                     when ((check pargs) ==  Safety || (proceed pargs)) $
                       do let safe = runFreshM $ safety ((check pargs) ==  Debug) bound listsys
                          printResult "Safety" safe
                     
                     else do selectColor False
                             putStrLn $ (gofile pargs)++" is not fenced"
                             setSGR [Reset]


-- separate :: M [Eqn] -> [M Eqn]
-- separate eqs = let fresh = runFreshM eqs
--                in L.map return fresh

getTypes :: [Eqn] -> M [GoType]
getTypes [] = return []
getTypes ((EqnSys bnd):xs) = do (defs, main) <- unbind bnd
                                rest <- getTypes xs
                                return (main:rest)


printResult :: String -> Bool -> IO()
printResult s t = do putStr $ s++": "
                     selectColor t
                     putStrLn $ show t
                     setSGR [Reset]

selectColor :: Bool -> IO()
selectColor True =  setSGR [SetColor Foreground Vivid Green]
selectColor False =  setSGR [SetColor Foreground Vivid Red]


proceed :: Checker -> Bool
proceed args = (check args == All) || (check args == Debug)
