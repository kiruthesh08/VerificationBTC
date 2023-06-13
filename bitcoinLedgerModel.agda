module bitcoinLedgerModel where

--open import bool
open import libraries.listLib
open import libraries.natLib
open import Data.Nat
open import Data.List
open import Data.Unit
open import Data.Bool
open import Data.Product
open import Data.Nat.Base
open import Agda.Builtin.Equality
open import Data.Empty

postulate n : ℕ
 
 

infixr 3 _+msg_

Time : Set
Amount : Set
Address : Set
TXID : Set
Signature : Set
PublicKey : Set

-- \bitcoinVersFive
Time       =  ℕ
Amount     =  ℕ
Address    =  ℕ
TXID       =  ℕ
Signature  =  ℕ
PublicKey  =  ℕ


-- \bitcoinVersFive
data Msg : Set where
   nat     :  (n : ℕ)         → Msg
   _+msg_  :  (m m' : Msg)     → Msg
   list    :  (l  : List Msg)  → Msg

postulate hashMsg : Msg → ℕ

postulate  publicKey2AddressUnimplemented :  (pubk : PublicKey)  → Address 
                                       
  

-- \bitcoinVersFive ADDD HERE 
publicKey2Address : (pubk : PublicKey) → Address
publicKey2Address 17 = 0
publicKey2Address 5 = 1
publicKey2Address 3 = 2 --ADDED
publicKey2Address 4 = 3 --ADDED 
publicKey2Address n = publicKey2AddressUnimplemented n -- unkown n 

-- Signed means that Msg msg has been signed
-- by private key corresponding to pubk

-- \bitcoinVersFive ADDD HERE

postulate SignedUnimplemented : (msg : Msg)(publicKey : PublicKey)(s : Signature) → Set


Signed : (msg : Msg)(publicKey : PublicKey)(s : Signature) → Set

Signed ((nat 5 +msg nat 0) +msg list ((nat 5 +msg nat 1) ∷ [])) 17 15 = ⊤                                                            -- 15 is the signature
Signed ((nat 10 +msg nat 0) +msg   list ((nat 12 +msg nat 2) ∷ (nat 5 +msg nat 3) ∷ [])) 17 8 = ⊤
                                                       -- (signature2)
Signed ((nat 7 +msg nat 1) +msg list ((nat 12 +msg nat 2) ∷ (nat 5 +msg nat 3) ∷ [])) 5 9 = ⊤
                                                       -- (signature3)

Signed ((nat 3 +msg nat 1) +msg list ((nat 5 +msg nat 4) ∷ (nat 2 +msg nat 5) ∷ (nat 8 +msg nat 6) ∷ [])) 5 6 = ⊤
       -- input                                               output                                                           (signature4)            publickey and address

Signed ((nat 8 +msg nat 2) +msg list ((nat 5 +msg nat 4) ∷ (nat 2 +msg nat 5) ∷ (nat 8 +msg nat 6) ∷ [])) 3 4 = ⊤

Signed ((nat 4 +msg nat 3) +msg list ((nat 5 +msg nat 4) ∷ (nat 2 +msg nat 5) ∷ (nat 8 +msg nat 6) ∷ [])) 4 5 = ⊤

-- Signed ((nat 4 +msg nat 3) +msg list ((nat 5 +msg nat 4) ∷ (nat 2 +msg nat 5) ∷ (nat 8 +msg nat 6) ∷ [])) 4 5 = ⊤

Signed msg publicKey s = SignedUnimplemented  msg publicKey s -- message corresponding to publickey and signature its false if not 15
                                                                                                        -- for some values its implemented for last its uniiplemeneted

record SignedWithSigPbk (msg : Msg)(address : Address) : Set where
 field publicKey  :  PublicKey
       pbkCorrect : publicKey2Address publicKey ≡ℕ  address
       signature  :  Signature
       signed     :  Signed msg publicKey signature


open SignedWithSigPbk public

{-
_≡PbkBool_ : (pubk pubk' : PublicKey) → Bool
pubk ≡PbkBool pubk' = publicKey2Address pubk  ≡ℕb publicKey2Address pubk'
-}

{- -- Unused but correct code

_≡Pbk_ : PublicKey → PublicKey → Set
key1 ≡Pbk key2 = T (key1 ≡PbkBool key2)
-}

-- \bitcoinVersFive
record TXField : Set where
  constructor txField
  field  amount     :  Amount
         address    :  Address

open TXField public

--\bitcoinVersFive
txField2Msg : (inp : TXField) → Msg
txField2Msg inp  =   nat (amount inp) +msg nat (address inp)

txFieldList2Msg : (inp : List TXField) → Msg
txFieldList2Msg inp  = list (mapL txField2Msg inp)


-- \bitcoinVersFive
txFieldList2TotalAmount : (inp : List TXField) → Amount
txFieldList2TotalAmount inp = sumListViaf amount inp

-- \bitcoinVersFive
record TXUnsigned : Set where
  field  inputs   : List TXField
         outputs  : List TXField

open TXUnsigned public

-- \bitcoinVersFive
txUnsigned2Msg :  (transac : TXUnsigned) → Msg
txUnsigned2Msg transac = txFieldList2Msg (inputs transac)  +msg txFieldList2Msg (outputs transac)

-- \bitcoinVersFive
txInput2Msg : (inp : TXField)(outp : List TXField) → Msg
txInput2Msg inp outp = txField2Msg inp +msg txFieldList2Msg outp

-- \bitcoinVersFive
tx2Signaux : (inp : List TXField) (outp : List TXField)  → Set
tx2Signaux []               outp  = ⊤
tx2Signaux (inp ∷ restinp)  outp  =
    SignedWithSigPbk (txInput2Msg inp outp) (address inp) ×  tx2Signaux restinp outp

tx2Sign : TXUnsigned → Set
tx2Sign tr = tx2Signaux (inputs tr) (outputs tr)


-- \bitcoinVersFive
record TX : Set where
  field  tx       :  TXUnsigned
         cor      : txFieldList2TotalAmount (outputs tx) ≦ txFieldList2TotalAmount (inputs tx)
         nonEmpt  : NonNil (inputs tx) × NonNil (outputs tx)
         sig      : tx2Sign tx

open TX public

Ledger : Set

-- \bitcoinVersFive
Ledger = (addr : Address) → Amount

initialLedger : Ledger
initialLedger addr = 0

-- \bitcoinVersFive
addTXFieldToLedger :  (tr : TXField)(oldLedger : Ledger) → Ledger
addTXFieldToLedger  tr oldLedger pubk =
         if   pubk ≡ℕb address tr then oldLedger pubk +  amount tr else oldLedger pubk

addTXFieldListToLedger  :  (tr : List TXField)(oldLedger : Ledger) → Ledger
addTXFieldListToLedger []        oldLedger  =  oldLedger
addTXFieldListToLedger (x ∷ tr)  oldLedger  =
      addTXFieldListToLedger tr (addTXFieldToLedger x oldLedger)


-- \bitcoinVersFive
subtrTXFieldFromLedger      :  (tr : TXField)       (oldLedger : Ledger)  →  Ledger
subtrTXFieldListFromLedger  :  (tr : List TXField)  (oldLedger : Ledger)  →  Ledger
subtrTXFieldFromLedger  tr oldLedger pubk =
         if   pubk ≡ℕb address tr then oldLedger pubk ∸  amount tr else oldLedger pubk

subtrTXFieldListFromLedger [] oldLedger = oldLedger
subtrTXFieldListFromLedger (x ∷ tr) oldLedger =
           subtrTXFieldListFromLedger tr (subtrTXFieldFromLedger x oldLedger)

-- \bitcoinVersFive
updateLedgerByTX :  (tr : TX)(oldLedger : Ledger) → Ledger
updateLedgerByTX tr oldLedger =  addTXFieldListToLedger (outputs (tx tr))
                                   (subtrTXFieldListFromLedger (inputs (tx tr)) oldLedger )


-- \bitcoinVersFive
correctInput : (tr : TXField) (ledger : Ledger) → Set
correctInput tr ledger = amount tr ≦ ledger (address tr)

-- \bitcoinVersFive
correctInputs : (tr : List TXField) (ledger : Ledger) → Set
correctInputs []        ledger  = ⊤
correctInputs (x ∷ tr)  ledger  = correctInput x ledger ×
                                  correctInputs tr (subtrTXFieldFromLedger x ledger)

correctTX : (tr : TX) (ledger : Ledger) → Set
correctTX tr ledger = correctInputs (inputs (tx tr)) ledger   -- was wrong   ******
                                                              -- was (outputs (tx tr))



UnMinedBlock : Set

-- \bitcoinVersFive
UnMinedBlock = List TX


-- \bitcoinVersFive
tx2TXFee : TX → Amount
tx2TXFee tr =
    txFieldList2TotalAmount (outputs (tx tr)) ∸ txFieldList2TotalAmount (inputs (tx tr))

unMinedBlock2TXFee : UnMinedBlock → Amount
unMinedBlock2TXFee bl = sumListViaf tx2TXFee  bl



-- \bitcoinVersFive
correctUnminedBlock : (block : UnMinedBlock)(oldLedger : Ledger)→ Set
correctUnminedBlock  []            oldLedger  = ⊤
correctUnminedBlock  (tr ∷ block)  oldLedger  =
    correctTX tr oldLedger ×  correctUnminedBlock  block (updateLedgerByTX tr oldLedger)

updateLedgerUnminedBlock : (block : UnMinedBlock)(oldLedger : Ledger) → Ledger
updateLedgerUnminedBlock []            oldLedger  = oldLedger
updateLedgerUnminedBlock (tr ∷ block)  oldLedger  =
    updateLedgerUnminedBlock block (updateLedgerByTX tr oldLedger)

BlockUnchecked : Set
BlockUnchecked = List TXField × UnMinedBlock

block2TXFee : BlockUnchecked → Amount
block2TXFee (outputMiner , block) = unMinedBlock2TXFee block

{-
upDateLedgerMining : (minerOutput  : List TXField)
                     (oldLedger : Ledger)
                     → Ledger
upDateLedgerMining minerOutput oldLedger =
           addTXFieldListToLedger minerOutput oldLedger
--              (txField reward miner)
-}

-- \bitcoinVersFive
correctMinedBlock : (reward : Amount)(block : BlockUnchecked)(oldLedger : Ledger) → Set

correctMinedBlock reward (outputMiner , block) oldLedger =
      correctUnminedBlock block oldLedger ×
      txFieldList2TotalAmount outputMiner ≡ℕ (reward + unMinedBlock2TXFee block)
--          (upDateLedgerMining reward miner )

-- \bitcoinVersFive
updateLedgerBlock : (block : BlockUnchecked)(oldLedger : Ledger)→ Ledger
updateLedgerBlock (outputMiner , block) oldLedger =
   addTXFieldListToLedger  outputMiner (updateLedgerUnminedBlock block oldLedger)

-- next blockchain
-- reward can be a function f : Time → Amount

BlockChainUnchecked : Set
BlockChainUnchecked = List BlockUnchecked

-- \bitcoinVersFive
CorrectBlockChain : (blockReward : Time → Amount)
                    (startTime : Time)
                    (sartLedger : Ledger)
                    (bc  : BlockChainUnchecked)
                    → Set
CorrectBlockChain blockReward startTime startLedger [] = ⊤
CorrectBlockChain blockReward startTime startLedger (block ∷ restbc)
   = correctMinedBlock (blockReward startTime) block startLedger
     ×  CorrectBlockChain blockReward (suc startTime)
        (updateLedgerBlock block startLedger)  restbc

-- \bitcoinVersFive
FinalLedger :  (txFeePrevious : Amount)     (blockReward : Time → Amount)
                (startTime : Time)           (startLedger : Ledger)
                (bc  : BlockChainUnchecked)  → Ledger
FinalLedger trfee blockReward startTime startLedger [] = startLedger
FinalLedger trfee blockReward startTime startLedger (block ∷ restbc) =
  FinalLedger (block2TXFee block) blockReward (suc startTime)
     (updateLedgerBlock block startLedger) restbc

-- \bitcoinVersFive
record BlockChain (blockReward : Time → Amount) : Set where
  field  blockchain  : BlockChainUnchecked
         correct     : CorrectBlockChain blockReward 0 initialLedger blockchain

open BlockChain public

blockChain2FinalLedger :  (blockReward : Time → Amount)(bc : BlockChain blockReward)
                           → Ledger
blockChain2FinalLedger blockReward bc =
   FinalLedger 0 blockReward 0 initialLedger (blockchain bc)

--\define reward function

myReward : Time → Amount
myReward zero = 50
myReward (suc zero) = 25
myReward (suc (suc zero)) = 12
myReward (suc (suc (suc t))) = 6


--\empty blockchain

bcemptyunchecked : BlockChainUnchecked
bcemptyunchecked = []


correctbcemptyunchecked : CorrectBlockChain myReward 0 initialLedger bcemptyunchecked
correctbcemptyunchecked = tt

bcempty : BlockChain myReward
blockchain bcempty = bcemptyunchecked
correct bcempty = correctbcemptyunchecked


--\ ledger after empty blockchain

ledgerafterempty : Ledger
ledgerafterempty = blockChain2FinalLedger myReward bcempty

--\ blockchain with 1 elem

block1 : BlockUnchecked
block1 .proj₁ = txField 50 0  ∷ []
block1 .proj₂ = []

bc1elem : BlockChainUnchecked
bc1elem = block1  ∷  []

bc1 : BlockChain myReward
blockchain bc1 = bc1elem
correct bc1 = (tt , tt) , tt


ledgerafterblock1 : Ledger
ledgerafterblock1 = blockChain2FinalLedger myReward bc1

-- proof of equality

block1at0proof :   ledgerafterblock1 0 ≡ 50                                -- 50! verfication provided
block1at0proof = refl
block1atsucproof : (n : ℕ) →
                 ledgerafterblock1 (suc n) ≡ 0
block1atsucproof n = refl
--
{- 
evaluation ledgerafterblock1 n 

if n ≡ℕb 0 then 50 else 0

ledgerafterblock1 (suc n) 

0

-}
-- blockchain with 2 elements
tx2Unsigned : TXUnsigned
inputs tx2Unsigned = txField 5 0 ∷ []
outputs tx2Unsigned = txField 5 1 ∷ []

tx2 : TX
tx tx2 = tx2Unsigned
cor tx2 = tt                                   -- sum of input is greater than sum of output
tx2 .nonEmpt .proj₁ = tt                   -- input list is nonempty
tx2 .nonEmpt .proj₂ = tt                    -- output list is non empty
publicKey (proj₁ (sig tx2)) = 17  -- mapped (hashed) to 0 address
pbkCorrect (proj₁ (sig tx2)) = tt   -- verfies above key
signature (proj₁ (sig tx2)) = 15
signed (proj₁ (sig tx2)) = tt
proj₂ (sig tx2) = tt                         -- sig is a list of signatures, this is sig for ramaining list of  element

--test =  Data.Nat._≤_ look up expression with ctrl .


block2 :  BlockUnchecked
proj₁ block2 = txField 25 1 ∷ []
proj₂ block2 = tx2 ∷ []


bc2elem : BlockChainUnchecked
bc2elem = block1 ∷  block2 ∷  []

bc2 : BlockChain myReward
blockchain bc2 = bc2elem
correct bc2 = (tt , tt) , ((((tt , tt) , tt) , tt) , tt)

ledgerafterblock2 : Ledger
ledgerafterblock2 = blockChain2FinalLedger myReward bc2

--  ledgerafterblock2 0  = 45
--  ledgerafterblock2 1  = 30
--  ledgerafterblock2 n  = 0   otherwise greater than equal to 2 

-- proof for block2

block2at0proof :   ledgerafterblock2 0 ≡ 45 -- 45!verfication provided
block2at0proof = refl

block2at1proof :   ledgerafterblock2 1 ≡ 30
block2at1proof = refl

block2atsucproof : (n : ℕ) → ledgerafterblock2 (suc( suc n)) ≡ 0 -- all nat of suc suc n evulate ledgerafterblock2 (suc( suc n))
block2atsucproof n = refl

{- 
result of evaluting ledgerafterblock2 n 

if n ≡ℕb 1 then
(if n ≡ℕb 1 then
 (if n ≡ℕb 0 then (if n ≡ℕb 0 then 50 else 0) ∸ 5 else
  (if n ≡ℕb 0 then 50 else 0))
 + 5
 else
 (if n ≡ℕb 0 then (if n ≡ℕb 0 then 50 else 0) ∸ 5 else
  (if n ≡ℕb 0 then 50 else 0)))
+ 25
else
(if n ≡ℕb 1 then
 (if n ≡ℕb 0 then (if n ≡ℕb 0 then 50 else 0) ∸ 5 else
  (if n ≡ℕb 0 then 50 else 0))
 + 5
 else
 (if n ≡ℕb 0 then (if n ≡ℕb 0 then 50 else 0) ∸ 5 else
  (if n ≡ℕb 0 then 50 else 0)))

result of evaluating result after  ledgerafterblock2 (suc( suc n))

0 

result of evaluating result after  ledgerafterblock2 (suc n)

if n ≡ℕb 0 then (if n ≡ℕb 0 then 5 else 0) + 25 else
(if n ≡ℕb 0 then 5 else 0)
-}

-- blockchain with 3 elements
tx3Unsigned : TXUnsigned
inputs tx3Unsigned = txField 10 0 ∷ txField 7 1 ∷ []
outputs tx3Unsigned = txField 12 2 ∷ txField 5 3 ∷ []

tx3 : TX
tx tx3 = tx3Unsigned
cor tx3 = tt                                             -- some of input is greater than somge of output
proj₁ (nonEmpt tx3) = tt                       -- input list is nonempty
proj₂ (nonEmpt tx3) = tt                             -- output list is non empty
publicKey (proj₁ (sig tx3)) = 17                     -- mapped (hashed) to 0 address
pbkCorrect (proj₁ (sig tx3)) = tt               -- verfies above key
signature (proj₁ (sig tx3)) = 8
signed (proj₁ (sig tx3)) = tt                      -- (signature2)
publicKey (proj₁ (proj₂ (sig tx3))) = 5       -- pubkey which maps to address
                                                                --5 (hashes + addition of check bits and version bit and maybe more)
pbkCorrect (proj₁ (proj₂ (sig tx3))) = tt
signature (proj₁ (proj₂ (sig tx3))) = 9        -- (signature3)
signed (proj₁ (proj₂ (sig tx3))) = tt
proj₂ (proj₂ (sig tx3)) = tt

block3 :  BlockUnchecked
proj₁ block3 = txField 12 2 ∷ []
proj₂ block3 = tx3 ∷ []


bc3elem : BlockChainUnchecked
bc3elem = block1 ∷  block2 ∷ block3 ∷  []


bc3 : BlockChain myReward
blockchain bc3 = bc3elem
correct bc3 = (tt , tt) , ((((tt , tt) , tt) , tt) , ((((tt , (tt , tt)) , tt) , tt) , tt))

ledgerafterblock3 : Ledger
ledgerafterblock3 = blockChain2FinalLedger myReward bc3

-- ledgerafterblock3 0  = 35
-- ledgerafterblock3 1  = 23
-- ledgerafterblock3 2  = 24
-- ledgerafterblock3 3  = 5
-- ledgerafterblock3 n  = 0   otherwise



--proof for block3

block3at0proof :   ledgerafterblock3 0 ≡ 35 -- 35!verfication provided
block3at0proof = refl

block3at1proof :   ledgerafterblock3 1 ≡ 23
block3at1proof = refl

block3at2proof :   ledgerafterblock3 2 ≡ 24
block3at2proof = refl

block3at3proof :   ledgerafterblock3 3 ≡ 5
block3at3proof = refl

block3atsucproof : (n : ℕ) → ledgerafterblock3 (suc( suc( suc( suc n)))) ≡ 0 -- all nat of suc suc n 
block3atsucproof n = refl
{-
ledgerafterblock3 n 

if n ≡ℕb 2 then
(if n ≡ℕb 3 then
 (if n ≡ℕb 2 then
  (if n ≡ℕb 1 then
   (if n ≡ℕb 0 then
    (if n ≡ℕb 1 then
     (if n ≡ℕb 1 then
      (if n ≡ℕb 0 then (if n ≡ℕb 0 then 50 else 0) ∸ 5 else
       (if n ≡ℕb 0 then 50 else 0))
      + 5
      else
... 600+ lines of statements 

ledgerafterblock3 (suc( suc( suc( suc n))))

0 


-}

-- blockchain with 4 elements

tx4Unsigned : TXUnsigned
inputs tx4Unsigned = txField 3 1 ∷ txField 8 2 ∷ txField 4 3 ∷ []  -- 15 total
outputs tx4Unsigned = txField 5 4 ∷ txField 2 5 ∷ txField 8 6  ∷ [] -- 15 total 

tx4 : TX
tx tx4 = tx4Unsigned
cor tx4 = tt                                                                  -- some of input is greater than some of output
proj₁ (nonEmpt tx4) = tt                                              -- input list is nonempty
proj₂ (nonEmpt tx4) = tt                                              -- output list is non empty
publicKey (proj₁ (sig tx4)) = 5                                      -- mapped (hashed) to 2 address ADDED new address 
pbkCorrect (proj₁ (sig tx4)) = tt
signature (proj₁ (sig tx4)) = 6                                   -- n allows for testing due to postulate 
signed (proj₁ (sig tx4)) = tt 
publicKey (proj₁ (proj₂ (sig tx4))) = 3
pbkCorrect (proj₁ (proj₂ (sig tx4))) = tt
signature (proj₁ (proj₂ (sig tx4))) = 4
signed (proj₁ (proj₂ (sig tx4))) = tt
publicKey (proj₁ (proj₂ (proj₂ (sig tx4)))) = 4           -- : publicKey2Address (publicKey (proj₁ (proj₂ (proj₂ (sig tx4)))))≡ℕ 3 address is 3 so key 4
pbkCorrect (proj₁ (proj₂ (proj₂ (sig tx4)))) = tt
signature (proj₁ (proj₂ (proj₂ (sig tx4)))) = 5
signed (proj₁ (proj₂ (proj₂ (sig tx4)))) = tt          -- make signed with ctrl u u c . 
proj₂ (proj₂ (proj₂ (sig tx4))) = tt 

block4 :  BlockUnchecked
proj₁ block4 = txField 3 3 ∷ txField 3 4 ∷  []
proj₂ block4 = tx4 ∷ []


bc4elem : BlockChainUnchecked
bc4elem = block1 ∷  block2 ∷ block3 ∷ block4 ∷ []

bc4 : BlockChain myReward
blockchain bc4 = bc4elem
correct bc4 = (tt , tt) , ((((tt , tt) , tt) , tt) , ((((tt , (tt , tt)) , tt) , tt) , ((((tt , (tt , (tt , tt))) , tt) , tt) , tt)))

ledgerafterblock4 : Ledger
ledgerafterblock4 = blockChain2FinalLedger myReward bc4

--{-
-- ledgerafterblock4 0  = 35
-- ledgerafterblock4 1  = 20
-- ledgerafterblock4 2  = 16
-- ledgerafterblock4 3  = 4
-- ledgerafterblock4 4  = 8 
-- ledgerafterblock4 5  = 2
-- ledgerafterblock4 6  = 8
-- ledgerafterblock4 n  = 0   otherwise

-- proof for block4

block4at0proof :   ledgerafterblock4 0 ≡ 35   --35
block4at0proof = refl


block4at1proof :   ledgerafterblock4 1 ≡ 20 --20
block4at1proof = refl

block4at2proof :   ledgerafterblock4 2 ≡ 16
block4at2proof = refl

block4at3proof :   ledgerafterblock4 3 ≡ 4
block4at3proof = refl

block4at4proof :   ledgerafterblock4 4 ≡ 8
block4at4proof = refl

block4at5proof :   ledgerafterblock4 5 ≡ 2
block4at5proof = refl

block4at6proof :   ledgerafterblock4 6 ≡ 8
block4at6proof = refl

block4atsucproof : (n : ℕ) → ledgerafterblock4 (suc( suc( suc( suc (suc( suc( suc( suc n)))))))) ≡ 0 -- all nat of suc suc n 
block4atsucproof n = refl

{-
-- evaluate

 ledgerafterblock4 (suc( suc( suc( suc (suc( suc( suc( suc n))))))))

0

 ledgerafterblock4 n

if n ≡ℕb 2 then
(if n ≡ℕb 1 then
 (if n ≡ℕb 4 then
  (if n ≡ℕb 3 then
   (if n ≡ℕb 2 then
    (if n ≡ℕb 1 then
     (if n ≡ℕb 0 then
      (if n ≡ℕb 0 then
       (if n ≡ℕb 1 then (if n ≡ℕb 0 then 12 else 0) + 5 else
        (if n ≡ℕb 0 then 12 else 0))
       + 12
       else
....... 200lines of statements 
    
-}
