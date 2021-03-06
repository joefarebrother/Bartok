{-# LANGUAGE TemplateHaskell, ScopedTypeVariables #-}
{-# OPTIONS_HADDOCK prune #-}
{-|
Module      : Tutorial
Description : A walkthrough of how to play Bartok.
-}
module Game.Bartok.Tutorial
 where
import Control.Lens ((^.),(%~),makeLenses, (%%~),(&),Lens'(..),Lens)
import Control.Monad (ap,liftM2)
import Control.Monad.Trans.State (StateT(StateT),evalStateT,runStateT)
import Data.Char (toLower,isSpace)
import Data.List (isPrefixOf,stripPrefix)
import qualified Data.List.NonEmpty as NE
import Data.List.NonEmpty(NonEmpty(..))
import Data.Map (Map)
import qualified Data.Map as Map (empty,findWithDefault,fromList,insert) -- (insert,findWithDefault,empty,fromList)
import Data.Maybe (listToMaybe)
import System.Random (StdGen,mkStdGen,split)
import System.Random.Shuffle (shuffle')

{- $doc
Note that this file involves copy-pasting a bunch of definitions so that it generates nice haddock.
It may be inaccurate or out of date.
-}

-- *Framework

-- | A Game is essentially a ruleset that defines how an event modifies the
-- gamestate.
type Game = Event -> GameState -> GameState
{-^
For example, in the following game nothing that happens has any effect:

    > useless :: Game
    > useless event state = state
-}
{-|
A game of Bartok, from the server's point of view, consists of
events arriving and affecting the gamestate.

Actions are the most interesting, and always come with a message (which may be the empty string). -}
data Event =
      Action Name Action String -- ^A player actually doing something (playing a card or drawing cards)
    | Timeout -- ^If no player has made an action for 10 seconds, this event will be sent.
    | PlayerJoin Name (Maybe (Name,Name))  -- ^This is handled by the base game. You probably want to leave it alone.
    | PlayerLeave Name -- ^A player leaving the game. Again handled by the base game.



{-| A game is a composition of rules
such as 'r1 (r2 (r3 useless))' .

For example, the following rule will stop players being penalized for timeouts.

> rLongTurns :: Rule
> rLongTurns oldgame Timeout gamestate = gamestate
> rLongTurns oldgame event gamestate = oldgame event gamestate

You usually want to call @oldgame event gamestate@ at some point
so that rules which have been implemented before yours get a chance to do something. -}
type Rule = Game -> Game

{-$doc
The rest of this tutorial is unfinished, and 'Game.Bartok.DataTypes' is a better reference.
See 'Game.Bartok.TLib' for a framework to make rules
and the source code of 'Game.Bartok.TSample' for sample rules using it.
-}

-- **Gamestate
{-
 One of the easiest things to do is award penalties 'Game.Bartok.TLib.penalty'
-}


-- | Transformations of gamestate.
type Step = GameState -> GameState


data Suit = Clubs | Diamonds | Hearts | Spades deriving (Show,Eq,Enum,Bounded,Ord)
data Rank = Ace | Two | Three | Four | Five | Six | Seven | Eight | Nine | Ten | Jack | Knight | Queen | King deriving (Show,Eq,Bounded,Ord)


-- | A single playing card
type Card = (Rank,Suit)

-- | An ordered collection of cards forming a player's hand
type Hand = [Card]

-- | Names of players.
type Name = String

-- | At any point, a player can attempt to take one of these actions
data Action =
      Draw Int -- ^ Draw some number of cards
    | Play Card -- ^ Play a card
     deriving (Show,Eq)




-- \ Identifiers for variables
type VarName = String

--TODO: make the documentation true (messages and lastMoveLegal)
-- | The state of a game in play
data GameState = GS {
       _players :: [Name], -- ^ The players curretly in the game. The player whose turn it is should be at head of list
       -- and usually this advances forward by 1 each turn.
       _hands :: Map Name Hand, -- ^ Stores the contents of each player's hand
       _deck :: [Card], -- ^ The deck from which cards are drawn
       _pile :: NonEmpty Card, -- ^ The cards that have been played - shuffled back into the deck when necessary.
       _messages :: [String], -- ^ The messages that .  Contains only those generated by the most recent event.
       _lastMoveLegal :: Bool, -- ^ Indicates if the last move was successful.
           -- When a new event happens, this is False until baseAct is called.

       _randg :: StdGen, -- ^ A seeded random number generator
       _winner :: Maybe Name, -- ^ @Nothing@ until a player p wins at which point it becomes @Just p@
       _varMap :: Map VarName Int -- ^ A store of named variables that rules may use to keep track of state between events.
     } deriving Show

-- I'll try not to expose casual readers to lenses.
-- They are fun and powerful, but arguably turn Haskell into a different language.
makeLenses ''GameState


-- ** View Rules

-- | A card as viewed - the type of cards sent to the client
data CardView = CardFace Card | CardBack deriving (Show)

-- | The structure describing data seen by players
data GameView = GV {
    _handsV :: [(Name,[CardView])] , -- ^ The players and the information a particular player will have about each hand.
    -- By default, this is a 'CardFace's for the viewing player and a number of 'CardBack's for others.
    _pileV :: [CardView] , -- ^ What should be seen of the pile. By default, only the top card is visible.
    _deckV :: [CardView] , -- ^ What should be seen of the pile. By default, none are visible.
    _messagesV :: [String] -- ^ The messages a player can see. By default, this is all messages that have been sent
} deriving Show
makeLenses ''GameView
-- handsV :: Lens' GameView [(Name,[CardView])]
-- handsV f gv@GV{_handsV = h} = (\h' -> gv{_handsV = h'}) <$> f h
-- deckV :: Lens' GameView  [CardView]
-- deckV f gv@GV{_deckV = d} = (\d' -> gv{_deckV = d'}) <$> f d
-- pileV :: Lens' GameView  [CardView]
-- pileV f gv@GV{_pileV = p} = (\p' -> gv{_pileV = p'}) <$> f p
-- messagesV :: Lens' GameView  [String]
-- messagesV f gv@GV{_messagesV = m} = (\m' -> gv{_messagesV = m'}) <$> f m

-- | Functions to tell a player what they should see
type Viewer = Name -> GameState -> GameView

-- | Rules that modify what players see without affecting the game state
type ViewRule = Viewer -> Viewer

-- | Complex rules
type Rule' = (Rule,ViewRule)



-- Enum instances

instance Enum Rank where
  toEnum i = case i of
    1 -> Ace
    2 -> Two
    3 -> Three
    4 -> Four
    5 -> Five
    6 -> Six
    7 -> Seven
    8 -> Eight
    9 -> Nine
    10 -> Ten
    11 -> Jack
    12 -> Knight
    13 -> Queen
    14 -> King
  fromEnum r = case r of
    Ace -> 1
    Two -> 2
    Three -> 3
    Four -> 4
    Five -> 5
    Six -> 6
    Seven -> 7
    Eight -> 8
    Nine -> 9
    Ten -> 10
    Jack -> 11
    Knight -> 12
    Queen -> 13
    King -> 14
  enumFrom n = map toEnum [fromEnum n..fromEnum (maxBound::Rank)]

next :: (Enum a, Bounded a, Eq a) => a -> a
next a = if a == maxBound then minBound else succ a
prev ::(Enum a, Bounded a, Eq a) =>  a -> a
prev a = if a == minBound then maxBound else pred a


instance (Enum a, Enum b, Bounded a, Bounded b, Eq a, Eq b) => Enum (a,b) where
  toEnum i = (\(x,y) -> (toEnum (x + fromEnum (minBound::a)),toEnum (y + fromEnum (minBound::b)))) $ i `divMod` (1+(fromEnum (maxBound::b) - fromEnum (minBound::b))) -- i `divMod` (fromEnum $ maxBound :: b)
  fromEnum (r,s) = (fromEnum r - fromEnum (minBound::a)) * (1+fromEnum (maxBound::b)-fromEnum (minBound::b)) + (fromEnum s - fromEnum (minBound::b))
  enumFrom c = c:(if c==maxBound then [] else enumFrom (succ c))

suitChar :: Suit -> Char
suitChar s = case s of
  Clubs -> 'C'
  Diamonds -> 'D'
  Hearts -> 'H'
  Spades -> 'S'

-- | Get the suit of a card.
suit :: Card -> Suit
suit = snd

-- | Get the rank of a card.
rank :: Card -> Rank
rank = fst

-- | One character corresponding to the rank (A1..9TJCQK)
rankChar :: Rank -> Char
rankChar r = (['A'] ++ [head $ show i | i <- [2..9]::[Int] ] ++ ['T','J','C','Q','K'])!!(fromEnum r - 1) -- UNSAFE

-- | Get the unicode playing card character corresponding to some card
uniCard :: Card -> Char
uniCard (r,s) = toEnum (0x1F0A0 + (fromEnum (maxBound::Suit) + fromEnum (minBound::Suit) - fromEnum s) * 16 + fromEnum r)

--reading cards

type Parser = StateT String Maybe
-- | Given 2 parsers, tries the first, if it fails, try the second
(<|>) :: Parser a -> Parser a -> Parser a
a <|> b = StateT (\s -> case runStateT a s of
    Just (x,s') -> Just (x,s')
    Nothing -> runStateT b s)--note that state is saved - Parsec does not do this for efficiency
runParser :: Parser a -> String -> Maybe a
runParser = evalStateT


parseRank :: Parser Rank
parseRank = StateT (\s ->
  fmap (\(r,c) -> (r,drop (length c) s)) $ listToMaybe $
    filter (\(_,c) -> isPrefixOf (map toLower c) (map toLower s))
      (map (\x -> (x,show x)) (enumFrom minBound) ++ map (\x -> (x,((:[]).rankChar) x)) (enumFrom minBound)))

parseSuit :: Parser Suit
parseSuit = StateT (\s ->
  fmap (\(r,c) -> (r,drop (length c) s)) $ listToMaybe $
    filter (\(_,c) -> isPrefixOf (map toLower c) (map toLower s))
      (map (\x -> (x,show x)) (enumFrom minBound) ++ map (\x -> (x,((:[]).suitChar) x)) (enumFrom minBound)))

ignore :: String -> Parser ()
ignore s = StateT (\s' -> let s'' = dropWhile isSpace s' in
                            let s''' = stripPrefix s s'' in
                              fmap ((,) () . dropWhile isSpace) s''')

parseCard :: Parser Card
parseCard = do
  r <- parseRank
  ignore "of" -- and possibly spaces either side
  s <- parseSuit
  return (r,s)


-- | Get the playeer if an event
eventPlayer :: Event -> Maybe Name
eventPlayer (Action p _ _) = Just p
eventPlayer (PlayerJoin p _) = Just p
eventPlayer Timeout = Nothing

-- | variable processing

readVar :: VarName -> GameState -> Int
readVar s gs = Map.findWithDefault 0 s (gs^.varMap)
setVar :: VarName -> Int -> Step
setVar s i = varMap %~ Map.insert s i
modifyVar :: VarName -> (Int -> Int) -> Step
modifyVar s f gs = setVar s (f $ readVar s gs) gs

-- | Shuffle the deck (does not touch the pile or hands) using the random seed contained in GameState.
shuffleDeck :: Step
shuffleDeck = uncurry ((deck%~).flip (ap shuffle' length)) . (randg %%~ split)
-- shuffleDeck = (deck /\ randg) %~ ap ((`ap` snd) . ((,) .) . (. fst) . liftM2 shuffle' fst (length . fst)) (split . snd)
-- shuffleDeck = (deck /\ randg) %~ (\(d,r) -> let (r1,r2) = split r in (shuffle' d (length d) r1,r2))

-- | Construct a new game from a list of player names.
newGame :: [String] -> GameState
newGame pls =  ((pile /\ deck) %~ (\(_,y:ys) -> (y:|[],ys))) . shuffleDeck $ -- UNSAFE
           GS { _deck = [ minBound.. ]
              , _pile = undefined
              , _messages = []
              , _lastMoveLegal = True
              , _randg = mkStdGen 0
              , _varMap = Map.empty
              , _players = pls  --[("Angus",[]),("Toby",[]),("Anne",[])]
              -- , _seats = pls
              , _hands = Map.fromList $ map (flip (,) []) (pls)
              --, _prevGS = Nothing
              , _winner = Nothing
              }



if' :: Bool -> a -> a -> a
if' b a c = if b then a else c

-- Thanks stack overflow
(/\)
    :: (Functor f)
    => ((a -> (a, a)) -> (c -> (a, c)))
    -- ^ Lens' c a
    -> ((b -> (b, b)) -> (c -> (b, c)))
    -- ^ Lens' c b
    -> (((a, b) -> f (a, b)) -> (c -> f c))
    -- ^ Lens' c (a, b)
(lens1 /\ lens2) f c0 =
    let (a, _) = lens1 (\a_ -> (a_, a_)) c0
        (b, _) = lens2 (\b_ -> (b_, b_)) c0
        fab = f (a, b)
    in fmap (\(a, b) ->
            let (_, c1) = lens1 (\a_ -> (a_, a)) c0
                (_, c2) = lens2 (\b_ -> (b_, b)) c1
            in c2
            ) fab

infixl 7 /\
