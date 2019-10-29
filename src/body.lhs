\section{Introduction}

\victor{Loose sentences follow; might even be wrong, sorry!}

  In this paper we discuss an Agda model of LibraBFT~\cite{Baudet2019} safety properties.
Our model is heavily based on the original paper's \emph{proof of safety}. The main
goal is to machine check the original author's proof that the set of all commits
seen by an honest node form a linear chain. In other words, the commit rule
is safe: no two blocks that match the commit rule will depend on conflicting pasts.

The LibraBFT is a pratical implementation of the \emph{HotStuff}~\cite{Yin2019} consensus
protocol.

\section{Abstract LibraBFT}

  In this section we go over the core constructions needed to
encode LibraBFT in Agda. We start with a small description
of how to work with hash functions in Agda, then \victor{...}
This sets the stage for our proofs~\Cref{sec:proof}.

\victor{I use the word ``chain'' later; would be good to give an idea of
what it means here}

\subsection{Epochs and Records and their Laws}

  In LibraBFT, time is divided in \emph{epochs}. Each epoch
has a configuration which dictates who is allowed to participate in consensus
for that epoch. The BFT assumptions states that the number of authors
in an epoch must always be greater than $3f$, where $f$ is the amount
of byzantine failures we want to withstand.

\begin{myhs}
\begin{code}
EpochId : Set
EpochId = Nat

record EpochConfig (f : Nat) : Set where
  field
    epochId  : EpochId
    authorsN : Nat
    isBFT    : suc (3 * f) <= authorsN

    seed     : Nat

  QuorumSize : Nat
  QuorumSize = authorsN MINUS f
\end{code}
\end{myhs}

  During an epoch the protocol is run in \emph{rounds}.  In each
round, one node is designated \emph{leader} and is responsible for
receiving and propagating requests from clients. Leaders are selected
deterministically from the current |EpochId| and round number.  The
set of nodes allowed to participate in a given epoch is fixed and
specified by the epoch configuration. We use a finite type for this
purpose.

\begin{myhs}
\begin{code}
Author : forall {f} -> EpochConfig f -> Set
Author ec = Fin (authorsN ec)
\end{code}
\end{myhs}

  A typical round of the LibraBFT protocol consists the leader
broadcasting a new \emph{block} to the participants. Each other node
will then verify whether the aforementioned block is valid and, when
that is the case, cast a vote.  When the leader receives enough votes,
it issues a \emph{quorum certificate} and broadcasts this
certificate. This certifies that the block which it refers has been
verified and concludes the round.  On the next round, another node
will be the leader and the process is repeated.

\victor{illustrate this stuff!}

  The nodes participating in consensus maintain a local tree of
\emph{records}. Whenever a node receives a certified block --- a block
followed by a quorum certificate for it -- it extends one of the
leaves of its tree of blocks. The root of the tree is a special
record, |Initial|. A path in this tree is denoted a \emph{chain}
and consists of blocks alternating with quorum certificates.
These are denoted in the original paper~\cite{Baudet2019}
by: $B_0 \leftarrow Q_0 \leftarrow B_1 \cdots$.
The |Record| datatype encapsulates the different kinds of
records. We will discuss the $\_\leftarrow\_$ relation shortly.

\begin{myhs}
\begin{code}
data Record : Set where
    I  : Initial -> Record
    B  : Block   -> Record
    Q  : QC      -> Record
\end{code}
\end{myhs}

  These different records correspond to network messages that
have already had their signatures, author and format checked.
Naturally, each of those contains specific data. \Cref{fig:records-def} shows
the complete definition. We record the fact that a record
has been created by a valid author by parametrizing everything
by an epoch config and taking authors directly from there.

  \victor{sloppy para; fix this}
  Although there are four different messages that nodes exchange throughout the
execution of LibraBFT --- blocks, votes, quorum certificates,
and timeouts --- we did not consider timeouts in our first model for they
pose no issue to safety \victor{why?}.  

\begin{figure}
\begin{myhs}
\begin{code}
data Initial : Set where
  mkInitial : Initial

module _ {f : Nat}(ec : EpochConfig f) where
record Block : Set where
  constructor mkBlock
  field
    bAuthor     : Author ec
    bCommand    : Command
    bPrevQCHash : QCHash
    bRound      : Round

record Vote : Set where
  constructor mkVote
  field
    vAuthor    : Author ec
    vBlockHash : BlockHash
    vRound     : Round
    vOrder     : ℕ 

record QC : Set where
 field
   qAuthor        : Author ec
   qBlockHash     : BlockHash
   qRound         : Round
   qVotes         : List BVote
\end{code}
\end{myhs}
\caption{Record Definitions}
\label{fig:records-defs}
\end{figure}

  The type of record chains is the central datatype in our development.
We seek to verify (in a machine-checkable manner) that the LibraBFT
protocol provides the safety guarantees their authors claim. These
safety guarantees culminate in lemma S6~\cite{Baudet2019}, which states
that blocks considered commited belong all to the \emph{same chain}.
That is, there is only one path from the root of the tree of records
that is extended through commits.

  A |RecordChain|, defined below, is essentially just a path in the tree. Differently
from the original work~\cite{Baudet2019}, where the authors denote any
path by \emph{chain}, we require these to extended explicitely all
the way to the root of the tree, represented by the initial record, |I|.
There is a fairly technical reason for this: we must only consider records
that belong in the record pool, i.e., have been received with a valid signature,
to take part in a chain. \victor{Shall we add that in the original paper
they imply this?} The |IsInPool : Record -> Set| is kept abstract throughout the
abstract model. We will come back to it in \Cref{sec:concrete-model-template}, for now,
we can think of a static, immutable pool of records we can use to construct
our chain. An inhabitant of |IsInPool r| indicates that |r| belongs to this pool.

\begin{myhs}
\begin{code}
data RecordChain : Record -> Set where
  empty  : forall {hi} -> RecordChain (I hi)
  step   : forall {r r'}
         -> (rc : RecordChain r) 
         -> r EXT r'
         -> Valid rc r' 
         -> {prf : IsInPool r'} 
         -> RecordChain r'
\end{code}
\end{myhs}

  Looking into |RecordChain| above we see that a record |r'| can only
be appended into a chain that ends in |r| iff |r EXT r'| and
|r'| is \emph{valid} w.r.t. said chain. The |EXTD| relation is only concerned 
with hashes, ensuring the \emph{previous hash} field of |r'| matches the
hash of |r|. The |Valid| predicate, on the other hand, is concerned with 
ensuring that the rounds increase correctly. It is defined in a |mutual|
block together with |RecordChain| and shown below.

\begin{myhs}
\begin{code}
data Valid : {r : Record} -> RecordChain r -> Record where
  ValidBlockInit : {b : Block}{hi : Initial} 
                 -> 1 <= bRound b -> Valid (empty {hi}) (B b)
  ValidBlockStep : {b : Block}{q : QC}
                 -> (rc : RecordChain (Q q))
                 -> qRound (qBase q) < bRound b
                 -> Valid rc (B b)
  ValidQC        : {q : QC} {b : Block}
                 -> (rc : RecordChain (B b))
                 -> qRound (qBase q) == bRound b
                 -> Valid rc (Q q)
\end{code}
\end{myhs}

  \victor{explain the |Valid| beast}
  
\subsubsection{Voting Constraints}

  Earlier we mentioned 
  

\subsection{Dealing with Cryptographic Hash Functions}

  We assume the existence of a cryptographic hash function throughout
our development. To capture this assumption, we use a module
parameter on the relevant modules: |hash : ByteString -> Hash|,
where |ByteString| is a list of booleans and |Hash| is an abstract datatype.
As is standard practice with hash functions, our reasoning here works modulo
hash collisions. To encode that, we borrow the techniques from Miraldo et al.~\cite{Miraldo2019},
where a hash collision is evidenced by the |HashBroke| datatype:

\begin{myhs}
\begin{code}
HashBroke : Set
HashBroke = exists (x , y) (Collision hash x y)

Collision : {A B : Set}(f : A -> B)(a1 a2 : A) -> Set
Collision f a1 a2 = a1 /= a2 TIMES f a1 == f a2
\end{code}
\end{myhs}

  Collision resistance of |hash| can be assumed via another module
parameter of type |CR hash|, defined below. This assumption provides
us with an injectivity principle for our abstract |hash| function that
works as expected: if the hash of two objects is the same, either the
objects are the same or we found a hash collision.

\begin{myhs}
\begin{code}
CR : (ByteString -> Hash) -> Set
CR hash = forall {x y} -> hash x == hash y -> Either (Collision hash x y) (x == y)
\end{code}
\end{myhs}

