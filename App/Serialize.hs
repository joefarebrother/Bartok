{-# LANGUAGE Trustworthy #-}
{-# LANGUAGE DeriveGeneric, StandaloneDeriving #-}

module Serialize(serialize, unserialize,readNewRule,
        ActionReq(..),Token,ClientPacket(..),NewRuleReq(..),
        getName,getTok)
 where

import GHC.Generics (Generic)
import qualified Data.ByteString.Lazy as L
import qualified Data.Text as T (unpack)
import Data.Aeson (FromJSON,ToJSON,defaultOptions,decode,encode,fromJSON,genericToEncoding,toEncoding,toJSON)

import DataTypes
import Views

deriving instance Generic GameView
deriving instance Generic CardView
deriving instance Generic Rank
deriving instance Generic Suit

deriving instance Generic Action
deriving instance Generic Event

instance ToJSON Rank where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON Suit where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON CardView where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON GameView where
  toEncoding = genericToEncoding defaultOptions

instance ToJSON Action where
  toEncoding = genericToEncoding defaultOptions
instance ToJSON Event where
  toEncoding = genericToEncoding defaultOptions

instance FromJSON Suit
instance FromJSON Rank
instance FromJSON Action
instance FromJSON Event

data ClientPacket = NewData Int GameView | NoNewData | Redirect String deriving (Show,Generic)
instance ToJSON ClientPacket

serialize :: ClientPacket -> L.ByteString
serialize = encode . toJSON


type Token = String

type CardIndex = Int

-- TODO: Consider adding some validation to player join requests (eg name can't contain silly characters)
data ActionReq = ReqPlay Name Token CardIndex String
               | ReqDraw Name Token Int String
               | ReqJoin Name Token
               | ReqLeave Name Token deriving (Show,Eq,Generic)
instance ToJSON ActionReq where toEncoding = genericToEncoding defaultOptions
instance FromJSON ActionReq

data NewRuleReq = NewRuleReq {
    imports :: [String],
    ruleType:: String,
    code :: String
} deriving(Show,Generic)

instance ToJSON NewRuleReq where toEncoding = genericToEncoding defaultOptions
instance FromJSON NewRuleReq

readNewRule :: L.ByteString -> Maybe NewRuleReq
readNewRule = decode

getName :: ActionReq -> Name
getName (ReqPlay p _ _ _) = p
getName (ReqDraw p _ _ _) = p
getName (ReqJoin p _) = p
getName (ReqLeave p _) = p

getTok :: ActionReq -> Token
getTok (ReqPlay _ t _ _) = t
getTok (ReqDraw _ t _ _) = t
getTok (ReqJoin _ t) = t
getTok (ReqLeave _ t) = t

unserialize :: L.ByteString -> Maybe ActionReq
unserialize = decode
-- unserialize s = do
--   name <- s ^? key "name" . _String . to T.unpack
--   action <- s ^? key "action" . _String
--   let messages = fromMaybe "" (s ^? key "messages" . _String . to T.unpack)
--   case action of
--     "draw" -> s ^? key "number" . _Integral >>= (\n -> return $ Action name (Draw n) messages)
--     "join" -> return $ PlayerJoin name
--     "play" -> do suit <- join $ s ^? key "card" . key "suit" . _String . to (readMaybe . showText)
--                  rank <- join $ s ^? key "card" . key "rank" . _String . to (readMaybe . showText)
--                  return $ Action name (Play (rank,suit)) messages
--     _ -> Nothing
