{-# LANGUAGE MultiWayIf #-}

module Sample where

import Lib
import DataTypes
import Control.Lens
import qualified Data.List.NonEmpty as NE
import Control.Monad
import Control.Arrow (second)

--all definitions work*
r8 :: Rule
--r8 = onLegalCard$ when' ((==Eight).rank) (fromStep nextTurn)
--r8 = onLegalCard (\card event gs -> if (rank card == Eight) then nextTurn gs else gs)
r8 = onLegalCard (\card event ->
    if rank card == Eight then nextTurn else doNothing)


--r8 = onLegalCard$ when ((==Eight).rank) nextTurn

rbase = const baseAct

ruleset = r8 (rq baseAct)


reverseDirection :: Step
reverseDirection = players %~ reverse

rq :: Rule --reverse direction on q, may have problems if reversing direction makes a move become illegal
-- rq act e gs = (onLegalCard$ when' ((==Queen).rank)
--                   (\e' gs' -> act e (reverseDirection gs))) act e gs
rq act e gs = onLegalCard (\ card event gs'->
                if (rank card == Queen)
                    then act e (reverseDirection gs)
                    else gs'
                ) act e gs


-- rq act e@(Action p (Play c) m) gs = if (rank c == Queen) then
--     if _lastMoveLegal (act e gs) then act e (reverseDirection gs)
--         else act e gs
--         else act e gs
-- rq act e gs = act e gs

--r8 = onLegalCard (\card event -> if (rank card == Queen) then reverseDirection else doNothing)

mustdo7 :: (Int->(Bool->Game)-> Rule)
mustdo7 n f = with (const$ head .(^.players)) (\p ->
              require (p,(Draw (2*n)), "thank you"++ (if n>1 then " "++ concat (replicate (n-1) "very ") ++ "much" else "")) f)

--counts the unresolved 7s
count7s :: GameState -> Int
count7s = readVar "sevens"

r7 :: Rule
r7 = with (const count7s) (\n -> if  n > 0
    then onDraw (\_->(mustdo7 n) (when' id (const$setVar "sevens" 0)))
       . onPlay (\c -> if rank c == Seven
        then onLegalCard$ (\c event ->
                 modifyVar "sevens" (+1)
               . mustSay ("have a "++join(replicate n "very ")++"nice day") event)
        else (mustdo7 n) (when' id (const$ broadcast "r7 unexpected")))
    else onLegalCard$ when' ((==Seven).rank)
             (\ e -> (modifyVar "sevens" (+1))
                   . (mustSay "have a nice day") e))

r7' :: Rule
r7' =  onAction (\(p,a,m) act e gs ->
         let count7 = readVar "sevens" gs
             veries = concat $ replicate count7 "very "
             veriesmuch = concat $ replicate (count7-1) "very " -- TODO: add the much
             gs' = act e gs in
         case a of
             (Draw n) | count7 > 0 , isTurn p gs ->
                 if n == 2*count7
                   then mustSay ("Thank you "++veriesmuch) e . setVar "sevens" 0 $ gs'
                   else penalty 1 ("Failure to draw "++show (2*count7)++" cards.") e gs
             (Play c) | gs'^.lastMoveLegal, rank c == Seven ->
                 mustSay ("Have a nice "++veries++"day") e . modifyVar "sevens" (+1) $ gs'
             (Play c) | gs'^.lastMoveLegal, count7 > 0 -> -- rank c /= Seven
                 penalty 1 ("Failure to draw "++show (2*count7)++" cards.") e gs
             _ -> gs')

                -- else onLegalCard (\card e->
                --     if (rank card == Seven)
                --       then modifyVar "sevens" (+1) . mustSay "have a nice day" e
                --       else doNothing)) act e gs

run7 :: Int -> Rule
run7 = undefined
