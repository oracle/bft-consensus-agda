open import LibraBFT.Prelude

module LibraBFT.Global.Network where

  -- Here we model the network as a predicate over NetworkRecords.  The only functionality is to
  -- produce an empty network with no messages, and to send a message.  We assume that messages may
  -- be dropped, duplicated and/or reordered.  Therefore, there is no reason to maintain an order,
  -- nor to explicitly drop messages.  We can process any message that has been sent at any time.
  -- Dropping a message is modeled simply by never processing it.  Similar to HashSet, for now we
  -- postulate something for this; we can fill out an implementation and prove the required
  -- properies later.

  module WithMsgType (A : Set) where

    postulate
      SentMessages : Set

      -- Predicates
      _∈SM_ : A → SentMessages → Set

      -- Functionality
      noMessages : SentMessages
      sendMsg    : SentMessages → A → SentMessages

      -- Properties
      ∈SM-noMessages-⊥ : {m : A} → m ∈SM noMessages → ⊥
      SM-send-correct  : {sm : SentMessages} {m : A}
                       → m ∈SM (sendMsg sm m)
      ∈SM-stable       : {sm : SentMessages} {m m' : A}
                       → m ∈SM sm
                       → m ∈SM (sendMsg sm m')
      SM-insert-target : {m m' : A} {sm : SentMessages}
                       → ¬ (m ∈SM sm)
                       → m ∈SM (sendMsg sm m')
                       → m ≡ m'

    sendMsgs : SentMessages → List A → SentMessages
    sendMsgs = foldr (flip sendMsg) 

    ∈SM-stable-list : ∀ {sm : SentMessages} {m : A}
                    → (msgs : List A)
                    → m ∈SM sm
                    → m ∈SM sendMsgs sm msgs
    ∈SM-stable-list {sm} {m} []        = subst (m ∈SM_) refl
    ∈SM-stable-list {sm} {m} (h ∷ t) prf = ∈SM-stable (∈SM-stable-list t prf)

  open WithMsgType
