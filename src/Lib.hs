{-- | Inefficient program to test UTXO input
      selection strategies.
--}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Lib where

import Data.IxSet.Typed as Ix
import Crypto.Hash
import System.IO.Unsafe (unsafePerformIO)
import System.Random
import Crypto.PubKey.Curve25519
import qualified Data.Text as T
import qualified Control.Foldl as F
import Test.QuickCheck
import Text.Tabl
import Data.Word
import Data.Proxy
import Data.Data
import qualified Data.ByteArray as BA

---------------------------------------------------------------------------
-- Nasty orphans & other horror stories.
instance Ord PublicKey where
  compare pk1 pk2 = BA.unpack pk1 `compare` BA.unpack pk2

instance Arbitrary PublicKey where
  arbitrary = pure newRandomPublicKey

newRandomPublicKey :: PublicKey
newRandomPublicKey = toPublic $ unsafePerformIO generateSecretKey
{-# NOINLINE newRandomPublicKey #-}

instance Data PublicKey where
  toConstr pk = toConstr (BA.unpack pk)
  dataTypeOf pk = dataTypeOf (BA.unpack pk)
  gunfold a b c = gunfold a b (toConstr (BA.unpack (fromConstr @PublicKey c)))

---------------------------------------------------------------------------
newtype Coin = Coin Word64 deriving (Eq, Ord, Enum, Num, Data)

instance Show Coin where
  show (Coin c) = show c

instance Bounded Coin where
  minBound = Coin 0
  maxBound = Coin (45 * 1000000000)

instance Arbitrary Coin where
  arbitrary = Coin <$> choose (minBound, maxBound)

---------------------------------------------------------------------------
newtype TxId = TxId (Digest SHA256)

---------------------------------------------------------------------------
type StakeIxs = '[Address, Coin, PublicKey]
data Stake = Stake {
    stakeAddress :: Address
  , stakeCoin :: Coin
  , stakePk :: PublicKey
  -- ^ The PublicKey of who owns the stake.
  } deriving (Ord, Eq, Show, Data)

instance Indexable StakeIxs Stake where
  indices = ixList
              (ixGen (Proxy @ Address))
              (ixGen (Proxy @ Coin))
              (ixGen (Proxy @ PublicKey))

---------------------------------------------------------------------------
-- | Ignoring any concern related to signing & verification.
data Tx = Tx {
    txInputs :: [Stake]
  , txOutputs :: [Stake]
  } deriving (Ord, Eq, Show, Data)

---------------------------------------------------------------------------
emptyTx :: Tx
emptyTx = Tx mempty mempty

---------------------------------------------------------------------------
-- The default Tx fee.
txFee :: Coin
txFee = Coin 200000 -- 0.20

---------------------------------------------------------------------------
data UTXO = UTXO (IxSet StakeIxs Stake)
  deriving (Eq, Ord, Show)

---------------------------------------------------------------------------
base58Alphabeth :: String
base58Alphabeth = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"

---------------------------------------------------------------------------
randomNames :: [T.Text]
randomNames = [ "Waylon Dalton"
              , "Justine Henderson"
              , "Abdullah Lang"
              , "Marcus Cruz"
              , "Thalia Cobb"
              , "Mathias Little"
              , "Eddie Randolph"
              , "Angela Walker"
              ]

---------------------------------------------------------------------------
-- | A useless virtuosism.
newtype WalletName = WalletName T.Text
  deriving (Eq, Ord, Show, Data)

instance Arbitrary WalletName where
  arbitrary = WalletName . (`mappend` "'s Wallet") <$> elements randomNames

---------------------------------------------------------------------------
-- | A base58-like address.
newtype Address = Address T.Text
  deriving (Eq, Ord, Show, Data)

instance Arbitrary Address where
  arbitrary = Address . T.pack <$> vectorOf 32 (elements base58Alphabeth)

---------------------------------------------------------------------------
-- | A User's crypto wallet, from which we can send or receive money.
data Wallet = Wallet {
    walletBalance :: Coin
  , walletName :: WalletName
  , walletOwner :: PublicKey
  } deriving (Ord, Eq, Show, Data)

type WalletIxs = '[PublicKey]
type Wallets = IxSet WalletIxs Wallet

instance Indexable WalletIxs Wallet where
  indices = ixList
              (ixGen (Proxy @ PublicKey))

instance Arbitrary Wallet where
  arbitrary = Wallet <$> arbitrary
                     <*> arbitrary
                     <*> arbitrary

type InputStake = Stake
type OutputStake = Stake

---------------------------------------------------------------------------
-- | An 'InputSelectionPolicy' is a function from the current 'UTXO' to
-- the list of input & outputs we picked.
type InputSelectionPolicy =  PublicKey
                          -> Coin
                          -> PublicKey
                          -> UTXO
                          -> ([InputStake], [OutputStake])


---------------------------------------------------------------------------
mkTx :: PublicKey
     -- ^ The sender of the payment.
     -> Coin
     -- ^ The amount of the payment.
     -> PublicKey
     -- ^ The receiver of the payment.
     -> InputSelectionPolicy
     -- ^ The input selection policy
     -> UTXO
     -- ^ The current UTXO
     -> (Tx, UTXO)
     -- ^ The new transaction and the updated UTXO.
mkTx sender amount receiver policy utxo =
  let (inputs, outputs) = policy sender amount receiver utxo
      tx = emptyTx { txInputs = inputs
                   , txOutputs = outputs
                   }
      in (tx, utxo)

--
-- The simulation
--

data StakeDistribution =
    CommunistDistribution
    -- ^ All the holders are given the same amount
    -- of stake.
  | WhalesDistribution
  -- ^ Big whales have 20% of stake assigned to
  -- them, the rest of the holders takes the rest.
  | AverageDistribution
  -- ^ Miscellanea of stake distributed
  -- randomly but almost evenly. No more
  -- than 5% of current stake is distributed
  -- amongs participants


data Env = Env {
    envUTXO :: UTXO
  , envWallets :: Wallets
  } deriving (Ord, Eq, Show)

--------------------------------------------------------------------------------
emptyEnv :: Env
emptyEnv = Env {
    envUTXO = UTXO mempty
  , envWallets = mempty
  }

--------------------------------------------------------------------------------
giveStakeTo :: PublicKey -> Coin -> Env -> Env
giveStakeTo a coin e@Env{..} =
  case Ix.getOne (envWallets @= a) of
    Nothing -> e
    Just old@Wallet{..} ->
      let new = old { walletBalance = walletBalance + coin }
      in e { envWallets = Ix.updateIx a new envWallets }

--------------------------------------------------------------------------------
allOwners :: Wallets -> [PublicKey]
allOwners = map walletOwner . Ix.toList

--------------------------------------------------------------------------------
-- | Distribute the initial stake.
distributeStake :: StakeDistribution -> Env -> Env
distributeStake distr env = case distr of
  CommunistDistribution -> communistDistr env
  WhalesDistribution -> whalesDistr env
  AverageDistribution -> averageDistr env

--------------------------------------------------------------------------------
-- | Each user gets an equal amount of stake.
communistDistr :: Env -> Env
communistDistr env@Env{..} =
  let owners = allOwners envWallets
      equalStake = floor ((fromIntegral (maxBound :: Word64)) /
                            ((fromIntegral (length owners)) :: Double)
                           )
  in F.fold (foldStake (Coin equalStake)) owners
  where
    foldStake :: Coin -> F.Fold PublicKey Env
    foldStake amount = F.Fold (\e o -> giveStakeTo o amount e) env id

--------------------------------------------------------------------------------
whalesDistr :: Env -> Env
whalesDistr env = go maxBound env
  where
    go :: Coin -> Env -> Env
    go _ e = e

--------------------------------------------------------------------------------
averageDistr :: Env -> Env
averageDistr env = go maxBound env
  where
    go :: Coin -> Env -> Env
    go _ e = e

--------------------------------------------------------------------------------
type UserAction = Env -> Env

--------------------------------------------------------------------------------
type Simulation = [UserAction]

--------------------------------------------------------------------------------
simulate :: Env -> Simulation -> Env
simulate initialEnv steps = foldl (flip ($)) initialEnv steps

--------------------------------------------------------------------------------
showReport :: Env -> IO ()
showReport _ =
  putStrLn $ T.unpack (tabl EnvAscii DecorAll DecorAll [AlignCentre] rows)
  where
    rows = headers : theData
    headers = ["Distribution"]
    theData = mempty
