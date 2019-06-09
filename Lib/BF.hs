module BF(rBF, rBFV)
 where
import TLib
import DataTypes
import Data.List.NonEmpty(NonEmpty(..))
import Views
import BaseGame hiding (isTurn, penalty)
import RuleHelpers(split)
--import Data.List(elemIndex)

-- utility functions --

swap = uncurry (flip (,))
cardToNum = fromEnum.swap -- swap so that incrementing the card increments the rank before the suit
numToCard = swap.toEnum


numToBF :: Int -> Char
numToBF = ((" +-<>,.[]"++repeat ' ') !!)

bfToNum :: Char -> Int
bfToNum = maybe 0 id . flip elemIndex " +-<>,.[]"

elemIndex x [] = Nothing
elemIndex x (y:ys) = if x==y then Just 0 else fmap(+1) $ elemIndex x ys

withPlayer :: (Name -> Rule) -> Rule
withPlayer f act e@(Action p _ _) gs = f p act e gs
withPlayer f act e gs = act e gs

withHand :: ([Card] -> Rule) -> Rule
withHand f = withPlayer $ \p -> with state $ \gs -> f (maybe [] id $ getHand p gs)

{-
-- copied from TLib
penalty :: Int -> String -> Game
penalty n reason (Action p a m) = draw n p . broadcast ("{} receives penalty {}: {}"%p%show n%reason)
penalty _ _ _ = id
-}

(!) :: Show a => VarName -> a -> VarName 
n ! x = n ++ "_" ++ show x


copyVar :: VarName -> VarName -> Step
copyVar from to gs = setVar to (readVar from gs) gs

copyMem :: VarName -> VarName -> Step
copyMem from to gs = 
    let l = readVar "BF_mem_left" gs
        r = readVar "BF_mem_right" gs in
    ( foldr (.) id [copyVar (from ! n) (to ! n) | n <- [l..r]]
    . copyVar (from++"_head") (to++"_head") 
    ) gs

copyStack :: VarName -> VarName -> Step
copyStack from to gs = 
    let ptr = readVar (from++"_pointer") gs in
    ( foldr (.) id [ 
              let l = readVar (from ! n) gs in
              ( copyVar (from ! n) (to ! n) 
              . copyVar (from++"_timeout" ! l) (to++"_timeout" ! l)
              ) | n <- [0..ptr]] 
     . copyVar (from++"_pointer") (to++"_pointer")
     ) gs

-- manipulating the interpreting player (i.e. managing a player-valued variable) --

setIntrPlayer :: Name -> Step
setIntrPlayer p = setVar ("BF_intpr_player_" ++ p) 1 . clearIntrPlayer

clearIntrPlayer :: Step
clearIntrPlayer gs = foldr ($) gs [setVar ("BF_intpr_player_" ++ p) 0 | p <- _players gs] 

getIntrPlayer :: GEGSto Name
getIntrPlayer _ _ gs = case filter check $ _players gs of
    [] -> error "Expected there to be an interpeting player!"
    [p] -> p
    _ -> error "Interpreting player in an inconsistent state!"
    where check p = readVar "BF_intr_player" gs /= 0

-- checks the player making this action
isIntrPlayer :: GEGSto Bool
isIntrPlayer act e@(Action p _ _) gs = boolVar ("BF_intr_player_" ++ p) act e gs
inIntrPlayer _ _ _ = False

-- rules --

rSetup :: Rule
rSetup = when (not_$ boolVar "BF_setup") (doBefore$ 
                setVar "BF_setup" 1
              . setVar "BF_pc" 1 -- pc needs to start at 1 since 0 is used to mean null
              . setVar "BF_prog_end" 1)

rDebug :: Rule
rDebug = 
    (withMessage $ \m ->
        case RuleHelpers.split m of
            ['!':v] -> with (getVar v) $ \val -> doBefore (broadcast (show val))
            _ -> id)
 . (when (boolVar "BF_input" ~&~ boolVar "BF_output") (doBefore $ broadcast "Inconsistent state!"))
{-. doBefore (\s -> broadcast ("Before: {}" % show (_players s)) s)
 . doAfter (\s -> broadcast ("After: {}" % show (_players s)) s) -}


rCards :: Rule
rCards = withCard $ \c -> 
    when (isLegal ~&~ (not_$ boolVar "BF_output")) $
    case (rank c) of
        Ace -> write ','
        Two -> write '.'
        Four -> write '+'
        Five -> write '-'
        Six -> write '<'
        Nine -> write '>'
        Ten -> write '['
        Jack -> write ']'
        _ -> id
    where write c = with (getVar "BF_prog_end") $ \end -> 
                        withPlayer (\p -> doBefore$ setIntrPlayer p)
                      . doBefore ( setVar ("BF_prog" ! end) (bfToNum c) 
                                . modifyVar ("BF_prog_end") (+1)
                             -- . setVar "BF_timeout" 100 -- we now timeout each loop individually
                                . copyMem "BF_mem" "BF_mem_backup" -- backup everything so it can be restored on an abort
                                . copyVar "BF_pc" "BF_pc_backup"
                                . copyStack "BF_stack" "BF_stack_backup"
                                )


restoreBackup :: Step
restoreBackup gs = let gs' = ( copyMem "BF_mem_backup" "BF_mem" 
                             . copyVar "BF_pc_backup" "BF_pc" 
                             . modifyVar "BF_prog_end" (subtract 1)
                             . copyStack "BF_stack_backup" "BF_stack"
                             . setVar "BF_input" 0
                             . setVar "BF_output" 1
                             ) gs 
                   in setVar ("BF_prog" ! (readVar "BF_prog_end" gs')) 0 gs'


rInterpret :: Rule
rInterpret = 
    withAction $ \_ -> -- don't trigger on timeouts
    when (not_ (boolVar "BF_input") ~&~ not_ (boolVar "BF_output")) $
    with (getVar "BF_pc") $ \pc ->
    whether (boolVar$ "BF_prog" ! pc) ( -- stop interpreting when we run out of program
        with (numToBF .: (getVar$ "BF_prog" ! pc)) (\instr -> 
        with (getVar$ "BF_mem_head") $ \head ->
        with (getVar$ "BF_mem" ! head) $ \mem->
        doBefore (modifyVar "BF_pc" (+1)) 
      . whether (boolVar "BF_skip")
                (case instr of 
                      '[' -> pushLoop pc . rInterpret
                      ']' -> popLoop $ \l -> when ((==l) .: getVar "BF_skip") (doBefore (setVar "BF_skip" 0)) . rInterpret
                      _ -> rInterpret) 
                (case instr of
                      '+' -> doBefore (modifyVar ("BF_mem" ! head) ((`mod` 56) . (+1))) . rInterpret
                      '-' -> doBefore (modifyVar ("BF_mem" ! head) ((`mod` 56) . (subtract 1))) . rInterpret
                      '>' -> doBefore ((modifyVar "BF_mem_head" (+1)) . (modifyVar "BF_mem_right" (`max` (head+1)))) . rInterpret
                      '<' -> doBefore ((modifyVar "BF_mem_head" (subtract 1)) . (modifyVar "BF_mem_left" (`min` (head-1)))) . rInterpret
                      ',' -> doBefore (setVar "BF_input" 1)
                      '.' -> doBefore ((setVar "BF_output" 1) . (setVar "BF_output_card" mem)) . giveOutputCard
                      '[' -> pushLoop pc . doBefore (setVar "BF_skip" (if mem == 0 then pc else 0)) . rInterpret
                      ']' -> popLoop $ \l -> whether (__$ mem/=0) (doBefore (setVar "BF_pc" l) . tickTimeout l) (clearTimeout l) . rInterpret
                      _ -> error "Expected a valid program"))
    ) {-else-} (doBefore clearIntrPlayer)

pushLoop :: Int -> Rule
pushLoop l = with (getVar "BF_stack_pointer") $ \sp -> 
             doBefore (setVar ("BF_stack" ! sp) l) 
           . doBefore (modifyVar "BF_stack_pointer" (+1))

popLoop :: (Int -> Rule) -> Rule
popLoop f = doBefore (modifyVar "BF_timeout" (subtract 1)) 
          . doBefore (modifyVar "BF_stack_pointer" (subtract 1)) 
          . with (getVar "BF_stack_pointer") ( \sp ->
            when (__$ sp < 0) ((doBefore$ modifyVar "BF_stack_pointer" (+1)) . (abort 1 "Syntax error"))
          . with (getVar$ "BF_stack" ! sp) f)

tickTimeout :: Int -> Rule
tickTimeout l = doBefore (modifyVar ("BF_stack_timeout" ! l) (+1))
              . when ((> 100) .: getVar ("BF_stack_timeout" ! l)) (abort 3 "Program took too long")

clearTimeout :: Int -> Rule
clearTimeout l = doBefore (setVar ("BF_stack_timeout" ! l) 0)

abort :: Int -> String -> Rule
abort n reason = doBefore restoreBackup . doOnly (illegal n reason)

rAbort :: Rule
rAbort = 
    when isTurn $
    when (said "ABORT") $
    abort 4 "Manual abort"

giveOutputCard :: Rule
giveOutputCard = 
    with getIntrPlayer $ \p ->
    with (numToCard .: getVar "BF_output_card") $ \c ->
    doBefore (\gs -> gs{_deck = c:_deck gs})
  . doBefore (draw1 p) 

-- Input and output --

{-
rPrepareIO :: Rule
rPrepareIO = 
   {- (when (boolVar "BF_input") $
       withPlayer $ \p-> 
       when isLegal $
       keepTurn p 
     . withHand (\h ->
         if length h <= 1 then doBefore ((draw1 p) . (broadcast$ "{} has too few cards to input, so draws 1"%p))
         else id))
  .-} (when (boolVar "BF_output") $ 
       with getIntrPlayer $ \p -> 
       when isLegal $
       keepTurn p 
     . with (numToCard .: getVar "BF_output_card") (\c ->
       doBefore (\gs -> gs{_deck = c:_deck gs})
     . doBefore (draw1 p)))  -- put the required card in their hand
  {-. (when (boolVar "BF_player_shift") $ -- restore player order that was messed with on the previous turn. Gets applied before we possibly mess with it again this turn.
       with (getVar "BF_player_shift") $ \n -> 
       when isLegal $
       doBefore (setVar "BF_player_shift" 0)
     . doAfter (modifyPlayers $ \ps ->
       let (l,r) = splitAt (n`mod`length ps) ps 
       in r++l)) -}
       

keepTurn :: Name -> Rule
keepTurn p = 
    withAction $ \a ->
    doAfter $ \gs ->
    let players = _players gs 
        (l, r) = break (== p) players
        n = length r 
        n' = if actionAdvancesTurn a then n-1 else n -- usual case: if we advanced the turn, n=1, else n=0 (mod length ps) ; so the usual case is to set this to 0
        gs' = modifyVar "BF_player_shift" (+n') gs
    in  gs'{_players = r ++ l} 

actionAdvancesTurn :: Action -> Bool
actionAdvancesTurn (Draw n) = n > 0
actionAdvancesTurn _ = True
-}

var7 :: VarName
var7 = "sevens"

ignoreR7 :: Rule
ignoreR7 = when (boolVar var7 ~&~ not_ (cardIs ((== Seven) . rank))) $
    doBefore (copyVar var7 "BF_7_backup")
  . doBefore (setVar var7 0)
  . doAfter (copyVar "BF_7_backup" var7)


rInput :: Rule
rInput = when (boolVar "BF_input") $
    withAction $ \a -> -- so we don't trigger on timeouts
    whether isIntrPlayer (
        withMessage $ \m -> 
        ignoreR7
      . when (cardIs$ const True) (doOnly $ illegal 1 "Attempting to play while inputting")
      . let ms = RuleHelpers.split m 
            ms' = filter (/= Nothing) $ map (runParser parseCard) ms in
        case ms' of 
            [] -> doBefore$ penalty 1 "Failure to name a card for input"
            [_,_] -> doBefore$ penalty 1 "Too many inputs"
            [Just c] -> withHand $ \h ->
                if not $ c `elem` h then doBefore$ penalty 1 "Inputting a card you don't have"
                else withPlayer $ \p -> 
                     with (getVar "BF_mem_head") $ \head ->
                     doBefore (cardFromHand' p c)
                   . doBefore (\gs -> gs{_pile= _pile gs `appendl` [c]}) -- put it on the bottom of the pile  
                   . case length h of 
                        0 -> doBefore (penalty 1 "Inputting your last card")
                        1 -> when (not_$ said "last card") $ doBefore (penalty 1 "Failure to declare \"last card\"") -- the last card rule only triggers on card plays
                        _ -> id               
                   . doBefore (setVar ("BF_mem" ! head) (cardToNum c))
                   . doBefore (setVar "BF_input" 0)
                   . doBefore (broadcast $ "{} inputs {}"%p%[uniCard c]) 
    )(with getIntrPlayer $ \p -> doOnly $ illegal 1 $ "Attempting to {} while {} is inputting" % show a % p)

rOutput :: Rule
rOutput = 
    (when (boolVar "BF_output") $
         withAction $ \a -> -- don't trigger on timeouts
         whether isIntrPlayer (
             withPlayer $ \p ->
             with (numToCard .: getVar "BF_output_card") $ \c ->
             ignoreR7
           . whether (cardIs (==c)) -- all this jankiness is to ensure that the move is legal; maybe there should be a better way to do that...
                     ( doBefore (cardToPile c) -- put a copy of the card on the pile to ensure this move is legal
                     . doBefore (setVar "BF_ghost_card" (cardToNum c)) -- this would be nicer if there were a way to just make a move legal while still passing through the inner rules...
                     . doBefore (setVar "BF_output" 0)
                     . doBefore (setVar "BF_output_card" 0)
                     . doAfter cleanupGhostCard
                     . doAfter (setVar "BF_output_cleanup" 1)
                     . makeInTurn p
                     )
                     (doOnly$ illegal 1 "Failure to output the correct card")
          )(with getIntrPlayer $ \p -> doOnly $ illegal 1 $ "Attempting to {} while {} is outputting" % show a % p))
    . (when (boolVar "BF_output_cleanup" ~&~ isLegal) $ 
            doAfter (setVar "BF_output_cleanup" 0)
          . doAfter cleanupGhostCard)

makeInTurn :: Name -> Rule
makeInTurn p = 
    with (_players .: state) $ \ps ->
    let (l,r) = break (== p) ps
        n = length r in
    doBefore (modifyPlayers $ const $ r++l)
  . doAfter (modifyPlayers $ \ps ->
        let (l,r) = splitAt (n-1) ps in r++l)

cleanupGhostCard :: Step
cleanupGhostCard gs =
  let c = numToCard (readVar "BF_ghost_card" gs) 
      pile = _pile gs in
  case pile of
     c1:|c2:cs | c2 == c -> gs{_pile = c1:|cs}
     _ -> gs -- edge cases might cause a physical copy of the card to enter the deck, such as when the deck gets shuffled from a penelty. I'm going to say this is a feature, not a bug.

-- Main rule --

rBF :: Rule
rBF = rDebug . rSetup . rAbort . rCards . rInput . rOutput . rInterpret

-- Veiws --

readProgram :: GameState -> (String, Int) 
readProgram gs = 
    let l = 1
        r = readVar "BF_prog_end" gs in
    ([numToBF $ readVar ("BF_prog" ! i) gs | i <- [l..r]], (readVar "BF_pc" gs)-l)


readMem :: GameState -> ([Card], Int)
readMem gs = 
    let l = readVar "BF_mem_left" gs
        r = readVar "BF_mem_right" gs 
        h = readVar "BF_mem_head" gs in
    ([numToCard $ readVar ("BF_mem" ! i) gs | i <- [l..r]], h-l+1) -- +1 to be consistent with readProgram, which already has its pc advanced by 1 by this point


rBFV :: ViewRule
rBFV v p gs = 
    let gv = v p gs 
        (prog, pc) = readProgram gs
        (mem, mc) = readMem gs
        (lp, rp) = splitAt pc prog
        (lm, rm) = splitAt mc mem
        msg = _messagesV gv
        m1 = lp ++ "#" ++ rp
        m2 = map uniCard lm ++ "#" ++ map uniCard rm 
        span = ("<span class=new>{}</span>"%)
        js = "<script>var old = $('.old'); old.next().remove(); old.remove(); $('.new').addClass('old')</script>"
     in
       gv{_messagesV = (map span [m1,m2++js]) ++ msg}







