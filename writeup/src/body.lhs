\section{Introduction}

\victor{Loose sentences follow; might even be wrong, sorry!}

  In this paper we discuss an Agda model of LibraBFT~\cite{Baudet2019} safety properties.
Our model is heavily based on the original paper's \emph{proof of safety}. The main
goal is to machine check the original author's proof that the set of all commits
seen by an honest node form a linear chain. In other words, the commit rule
is safe: no two blocks that match the commit rule will depend on conflicting pasts.

The LibraBFT is a pratical implementation of the \emph{HotStuff}~\cite{Yin2019} consensus
protocol.



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

\section{The Model}

  Before delving into the components of LibraBFT and how they were
encoded in our model, it is worth looking at the high level
architecture.  A node participating in the LibraBFT network sends and
receives messages and consequently, transition its internal state,
first from $s_0$ to $s_1$, then to $s_2$ and so on and so forth. A
concrete model, proving that an imlementation of the protocol is
correct, that is, all the possible states we can reach will satisfy
certain safety properties -- committed entries never conflict
(\Cref{thm:s5}) -- would proceed by proving that the state transitions
preserve the necessary invariants. These invariants, which have been
proven to guarantee \Cref{thm:s5}, are provided by the abstract model,
\Cref{sec:abstract-librabft}. We say that a given state |RSS| 
satisfy these invariants through |SafeRSS| (\Cref{sec:main-safety-theorem}).

  When implementing the concrete interface, \Cref{sec:concrete-librabft},
which would carry the actual implementation of the node,
one would implement an \emph{insert} function. This is the function
that receives previously validated records and adds them to 
the (concrete) store of the participant.

\begin{myhs}
\begin{code}
insertValidRecord : (rss : RecordStoreState) -> ValidRecord rss -> RecordStoreState
\end{code}
\end{myhs}

  To prove that this implementation is correct, we prove it respects
the invariants required by the abstract model and conjure the necessary properties.
We will look at this in more detail in \Cref{sec:concrete-librabft}, but
it looks somewhat like the following:

\begin{myhs}
\begin{code}
insert-isValid  : (rss : RecordStoreState)(r : ValidRecord rss)
                -> SafeRSS rss
                -> SafeRSS (insertValidRecord rss r)
\end{code}
\end{myhs}

\subsection{Abstract LibraBFT}
\label{sec:abstract-librabft}

  In this section we go over the core constructions needed to
encode the LibraBFT invariants in |SafeRSS| and prove that they imply
the necessary safety properties. 

\subsubsection{Epochs and Records}

  In LibraBFT, time is divided in \emph{epochs}. Each epoch
has a configuration which dictates who is allowed to participate in consensus
for that epoch. The BFT assumptions states that the overall number of authors
in an epoch must always be greater than $3f$, where $f$ is the amount
of byzantine failures we wish to withstand.

\begin{myhs}
\begin{code}
EpochId : Set
EpochId = Nat

record EpochConfig (f : Nat) : Set where
  field
    epochId   : EpochId
    authorsN  : Nat
    isBFT     : suc (3 * f) <= authorsN

    seed      : Nat

  QuorumSize  : Nat
  QuorumSize  = authorsN MINUS f
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

  The properties we wish to prove often require the
existence of ``an honest author'' in a given set of authors. 
This is important as it is the only way to assume
that at least one author has been abiding by the
rules of the protocol (\Cref{sec:voting-constraints}).
Consequently, we must bring the notion of \emph{honest} into our model. 
Given that we must not be able to inspect who is honest or not, we
encode this as a postulate. In order to estabilish the
honest of a node, then, one must rely on the classic BFT lemma, 
also wirten as a postulate in our model.

  The classic BFT lemma states that for every two quorums of nodes,
that is, a subset of nodes whose combined voting power is at least
|QuorumSize|, there exists at least one honest node that belongs to
both quorums. Our |lemmaB1| below encodes the BFT assumption --- a |QC|
denotes a quorum certificate and |a inQC q| indicates |a|
has voted in |q|, as we shall see shortly.

\begin{myhs}
\begin{code}
postulate
  Honest   : forall {f}{ec : EpochConfig ec} -> Author ec -> Set
  lemmaB1  : (q1 q2 : QC) -> exists (a) (a inQC q1 TIMES a inQC q2 TIMES Honest a)
\end{code}
\end{myhs}

\victor{I feel we might need more info on honest nodes vs dishonest ones; 
For that though, I need to find a better mental model}

\begin{figure}
\victor{finish this figure!}
\centering
\resizebox{.8\textwidth}{!}{%
\begin{tikzpicture}
\node (node1) {$\mathit{node}_1$};
\node [below = .3cm of node1] (node2) {$\mathit{node}_2$};
\node [below = .3cm of node2] (node3) {$\mathit{node}_3$};
\node [below = .3cm of node3] (node4) {$\mathit{node}_4$};
\node [right = .5cm of node1] (e11) {};
\node [right = .5cm of node2] (e12) {};
\node [right = .5cm of node3] (e13) {};
\node [right = .5cm of node4] (e14) {};
\node [right = 1cm of e11] (e21) {};
\node [right = 1cm of e12] (e22) {};
\node [right = 1cm of e13] (e23) {};
\node [right = 1cm of e14] (e24) {};
\node [right = 1cm of e21] (e31) {};
\node [right = 1cm of e22] (e32) {};
\node [right = 1cm of e23] (e33) {};
\node [right = 1cm of e24] (e34) {};
\node [right = 1cm of e31] (e41) {};
\node [right = 1cm of e32] (e42) {};
\node [right = 1cm of e33] (e43) {};
\node [right = 1cm of e34] (e44) {};
\node [right = 1cm of e41] (e51) {};
\node [right = 1cm of e42] (e52) {};
\node [right = 1cm of e43] (e53) {};
\node [right = 1cm of e44] (e54) {};
\node [right = 1cm of e51] (e61) {};
\node [right = 1cm of e52] (e62) {};
\node [right = 1cm of e53] (e63) {};
\node [right = 1cm of e54] (e64) {};
\node [right = 1cm of e61] (e71) {};
\node [right = 1cm of e62] (e72) {};
\node [right = 1cm of e63] (e73) {};
\node [right = 1cm of e64] (e74) {};

\draw[-] (node1.east) -- ($ (e71) + (1,0) $);
\draw[-] (node2.east) -- ($ (e72) + (1,0) $);
\draw[-] (node3.east) -- ($ (e73) + (1,0) $);
\draw[-] (node4.east) -- ($ (e74) + (1,0) $);

\draw[->] (e12) -- (e21);
\draw[->] (e12) -- (e23);
\draw[->] (e12) -- (e24);
\draw[->] (e21) -- (e32);
\draw[->] (e23) -- (e32);
\draw[->] (e24) -- (e32);
\draw[->] (e32) -- (e41.west);
\draw[->] (e32) -- (e43.west);
\draw[->] (e32) -- (e44.west);

\draw[->] (e44.east) -- (e51);
\draw[->] (e44.east) -- (e52);
\draw[->] (e44.east) -- (e53);
\draw[->] (e51) -- (e64);
\draw[->] (e52) -- (e64);
\draw[->] (e53) -- (e64);
\draw[->] (e64) -- (e71);
\draw[->] (e64) -- (e72);
\draw[->] (e64) -- (e73);

\draw[dashed] ($ (e11) + (-.1,1) $)
          --  ($ (e14) + (-.1,-1) $);

\draw[dashed] ($ (e41) + (0,1) $)
           -- ($ (e44) - (0,1) $);

\draw[dashed] ($ (e71) + (0,1) $)
           -- ($ (e74) - (0,1) $);

\node at ($ (e14)!0.5!(e44) - (0,1) $) {$\mathit{round}\;n$};
\node at ($ (e44)!0.5!(e74) - (0,1) $) {$\mathit{round}\;(n+1)$};
\end{tikzpicture}}
\caption{Simplified overview of the consecutive rounds of LibraBFT
after round synchorinization has settled.}
\label{fig:librabft-simplified-execution}
\end{figure}

  A typical round of LibraBFT, illustrated in
\Cref{fig:librabft-simplified-execution}, consists in the leader
broadcasting a new \emph{block} to the other notes. Each other node
will then verify whether the aforementioned block is valid and, when
that is the case, cast a vote.  When the leader receives enough votes,
it issues a \emph{quorum certificate}, which consists in a set of votes, 
and broadcasts this
certificate. This certifies that the block which it refers has been
verified and concludes the round.  On the next round, another node
will be the determined leader and the process is repeated. 

  The nodes participating in consensus maintain a pool of
\emph{records}. How this pool is implemented is uninportant,
hence, we abstract it by a type supporting
a predicate that indicates whether a record belonds in
the pool, as shown with |isRecordStoreState| below.
We require the |isInPool| predicate to be proof irrelevant for
technical reasons: we will be storing inhabitants of |isInPool|
on some auxiliary proof objects throughout our model and
we must be able to rewrite them freely. 
\victor{more info on it? I don't wanna get too technical too fast}

%format isInPoolirrelevant = "\HV{\wdw{isInPool}{irrelevant}}"
\begin{myhs}
\begin{code}
  record isRecordStoreState {a}(RSS : Set a) : Set (suc a) where
    constructor rss
    field
      isInPool            : Record -> Set
      isInPoolirrelevant  : forall {r}(p0 p1 : isInPool r) -> p0 == p1
\end{code}
\end{myhs}

  This pool of records is logically organized a tree rooted in
the initial record. The edges of the tree indicate that a record
\emph{extends} another. Naturally, records are only allowed to
extend records that are either in the pool or are the initial record.
This \emph{extends} relation is written |EXTD| and illustrated in
\Cref{fig:recordstorestate}. We postpone its Agda definition until
\Cref{sec:record-chain}.

\begin{figure}
\centering
\resizebox{.8\textwidth}{!}{%
\begin{tikzpicture}[txt/.style={scale=1.6}]
\node [txt] (hinit) {|hi|};
\node [txt, right = of hinit] (b0) {|b0|};
\node [txt, right = of b0]   (q0) {|q0|};
\node [txt, right = of q0]   (b1) {|b1|};
\node [txt, right = of b1]   (q1) {|q1|};
\node [txt, above = of b1]   (b2) {|b2|};
\node [txt, right = of b2]   (q2) {|q2|};
\node [txt, right = of q1]   (b3) {|b3|};
\node [txt, right = of b3]   (q3) {|q3|};
\node [txt, below = of b3]   (b4) {|b4|};
\node [txt, right = of b4]   (q4) {|q4|};
\node [txt, right = of q3]   (b5) {|b5|};
\node [txt, right = of b5]   (q5) {|q5|};
\node [txt, right = of q4]   (b6) {|b6|};
\node [txt, right = of b6]   (q6) {|q6|};

\draw[->] (q6) -- (b6);
\draw[->] (b6) -- (q4);
\draw[->] (q4) -- (b4);
\draw[->] (b4) to[in=270 , out=180] (q1);
\draw[->] (q5) -- (b5);
\draw[->] (b5) -- (q3);
\draw[->] (q3) -- (b3);
\draw[->] (b3) -- (q1);
\draw[->] (q1) -- (b1);
\draw[->] (b1) -- (q0);
\draw[->] (q0) -- (b0);
\draw[->] (b0) -- (hinit);
\draw[->] (q2) -- (b2);
\draw[->] (b2) to[in=90 , out=180] (q0);

\node (box) [fit=(b0) (q2) (q6) , draw , dashed, rounded corners=2mm] {};
\node at (box.north) [scale = 1.6, above, inner sep=1mm] 
  {\textit{Record Pool}}; 

\draw [dotted] (hinit.south) -- ($ (q1.south) - (0.5,0) $)
               to[out=270, in=180] (b4.north) -- (q6.north);
\node at (b6.north) [scale = 1.6, above , inner sep=1mm] {\textit{RecordChain}};

\end{tikzpicture}}
\caption{A abstract record store state, inside the dashed box, 
with its records ordered as a tree. A |RecordChain q6| is shown in a 
dotted line. Records have their rounds as a subscript}
\label{fig:recordstorestate}
\end{figure}


Whenever a node receives a certified block -- a block
followed by a valid quorum certificate -- it adds it
to its pool extending one of leaves of the tree of blocks. 
A path in this tree is denoted a |RecordChain|
and consists of blocks alternating with quorum certificates.
These are denoted in the original paper~\cite{Baudet2019}
by: $B_0 \leftarrow Q_0 \leftarrow B_1 \cdots$.
The |Record| datatype encapsulates the different kinds of
records, which is required to provide a homogeneous treatment of $\_\leftarrow\_$.

\begin{myhs}
\begin{code}
data Record : Set where
  I  : Initial  -> Record
  B  : Block    -> Record
  Q  : QC       -> Record
\end{code}
\end{myhs}

  These different records correspond to network messages that
have already had their signatures, author and format checked.
Naturally, each of those contains specific data.
We record the fact that a record
has been created by a valid author by parametrizing everything
by an epoch config and taking authors directly from there. 
We also store the necessary checks to ensure that a quorum certificate is valid,
namely: (1) no duplicate votes are present; (2) we have at least |QuorumSize ec|
votes; (3) all votes vote for the same block and (4) all votes happened on the same
round. All the records can be seen in \Cref{fig:record-defs}.
The original paper~\cite{Baudet2019} also defines timeouts
as a record. We did not consider timeouts in our first model for they pose no issue
to safety. They are simply a mechanism to prevent a dishonest leader to stop progress.
\victor{more on timeouts?}

\begin{figure}
\begin{myhs}
\begin{code}
data Initial : Set where
  mkInitial : Initial

module _ {f : Nat}(ec : EpochConfig f) where
  record Block : Set where
    constructor mkBlock
    field
      bAuthor       : Author ec
      bCommand      : Command
      bPrevQCHash   : QCHash
      bRound        : Round

  record Vote : Set where
    constructor mkVote
    field
      vAuthor       : Author ec
      vBlockHash    : BlockHash
      vRound        : Round
      vOrder        : Nat        -- Used to impose invariants; not in original paper.

  record QC : Set where
   field
     qAuthor        : Author ec
     qBlockHash     : BlockHash
     qRound         : Round
     qVotes         : List Vote
     qVotesC1       : IsSorted (\ v0 v1 -> vAuthor v0 <Fin vAuthor v1) qVotes
     qVotesC2       : QuorumSize ec <= length qVotes
     qVotesC3       : All (\ v -> vBlockHash v == qBlockHash qBase)  qVotes
     qVotesC4       : All (\ v -> vRound v == qRound qBase)          qVotes
\end{code}
\end{myhs}
\caption{Record Definitions}
\label{fig:record-defs}
\end{figure}

\subsubsection{Record Chains and the Commit Rule}
\label{sec:record-chains}

  Record chains, informally introduced in \Cref{fig:recordstorestate},
represent an sequence of blocks extending one another in a
participants state.  A record chain into a record |r| is a path from
the initial record into |r| through the tree of records that nodes
keep locally. Naturally, one can only use valid records to build these
chains. In this section we explore what does it mean for a record to
be valid and how we encoded this in Agda. In fact, the type of record
chains is the central datatype in our development. 

  A value of type |RecordChain r| is a proof that we can build a path from
the initial record into |r|, using only the records in a given record store state.
The dependency on a given record store state is important: one must not conjure
records to satisfy dependencies while proving theorems. The |RecordChain| datatype
will then be parametrized by an arbitrary record store state and contain two
constructors -- one representing the empty chain, and another representing
a chain that contains at least one valid record on its tail.
 
\begin{myhs}
\begin{code}
module Abstract (RSS : Set)(isRSS : isRecordStoreState RSS) where
  data RecordChain  : Record -> Set where
    empty  : forall {hi} -> RecordChain (I hi)
    step   : forall {r r'}(rc : RecordChain r) 
           -> r EXT r'
           -> {prf : isInPool isRSS r'} 
           -> RecordChain r'
\end{code}
\end{myhs}

  We say that a record |r'| is valid with respect to |r|, hence, it can extend an existing
record chain |rc : RecordChain r|, whenever |r'| has its |prevHash| field
correctly set to |hash r| and the rounds where |r| and |r'| were issued
are correctly related. We use the datatype |r EXT r'| to capture both contraints.
The |EXTTRD| type is the reflexive-transitive closure of |EXT|.

\begin{myhs}
\begin{code}
module Abstract (RSS : Set)(isRSS : isRecordStoreState RSS) where
  data EXTD : Record -> Record -> Set where
   IEXTB  : {i : Initial} {b : Block}
          -> 1 <= bRound b
          -> HashR (I i) ==  bPrevQCHash b
          -> I i EXT B b
   QEXTB  : {q : QC} {b : Block}
          -> qRound < bRound b
          -> HashR (Q q) ==  bPrevQCHash b
          -> Q q EXT B b
   BEXTQ  : {b : Block} {q : QC}
          -> qRound q == bRound b
          -> HashR (B b) ==  qBlockHash q
          -> B b EXT Q q

  data EXTTRD (r0 : Record) : Record -> Set where
   ssRefl  : r0 EXTTR r0
   ssStep  : forall {r1 r2 : Record} -> (r0 EXTTR r1) -> (r1 EXT r2) -> r0 EXTTR r2
\end{code}
\end{myhs}
  
  It is important to note that the original work~\cite{Baudet2019}
describes a number of other validation conditions (Section 4.2). We
stress that the majority of those are assumed to have been checked
at this stage. The conditions directly relevant to
the safety properties, which we have brought
into our model, are the monotonicity of round numbers and hash
chaining, which are expressed in |EXTD| above.

  Another way of thinking about the |EXTD| relation is in terms of
dependency. A value of type |r0 EXT r1| proves that |r1| depends on |r0|.
Which brings us to our first lemma: all valid records depend on the initial
record:

\begin{myhs}
\begin{code}
lemmaS11 : {i : Initial}{r : Record} -> RecordChain r -> (I i) EXTTR r
\end{code}
\end{myhs}

  The proof of |lemmaS11| goes by induction on |RecordChain|, extracting the
|EXTD| fields and building |EXTTRD|. A second, more interesting lemma,
states the injectivity of |EXTD|. Again, its proof is simple and depends
solely on the injectivity of the hash function, modulo hash collisions.

\begin{myhs}
\begin{code}
lemmaS12 : forall {r0 r1 r2} -> r0 EXT r2 -> r1 EXT r2 -> Either HashBroke (r0 == r1)
\end{code}
\end{myhs}

  A third lemma states that for whatever record |r2| that
comes to depend on two others, |r0| and |r1|, then these two others must
also be dependent. As expected, this is only true modulo hash collisions.

\begin{myhs}
\begin{code}
lemmaS13  : ∀{r0 r1 r2} -> RecordChain r0 -> RecordChain r1
          -> r0 EXTTR r2 -> r1 EXTTR r2
          -> round r0 < round r1
          -> Either HashBroke (r0 EXTTR r1)
\end{code}
\end{myhs}

  These three lemmas estabilish a base for reasoning over the
more intricate propositions we want to look into next. Before
that, though, we must construct one last notion in Agda: that
of at least $k$ certified blocks in the tail of a record chain.
(Section 5.2 in the original paper~\cite{Baudet2019}) --- denoted
a $k$-chain, defined below. The definition
might seem intricate, but it is simply unfolding $k$ steps in a
record chain. 

\begin{myhs}
\begin{code}
module Abstract (RSS : Set)(isRSS : isRecordStoreState RSS) where
  data Kchain (R : Record -> Record -> Set) 
    : (k : Nat){r : Record} -> RecordChain r -> Set1 where
      zchain  : forall {r}{rc : RecordChain r} -> Kchain R 0 rc
      schain  : forall {k r}{rc : RecordChain r}{b : Block}{q : QC}
              -> (rb    : r   ← B b)
              -> {prfB  : IsInPool (B b)}
              -> (prf   : R r (B b))
              -> (bq    : B b ← Q q)
              -> {prfQ  : IsInPool (Q q)}
              -> Kchain R k rc
              -> Kchain R (suc k) (step (step rc r←b {prfB}) b←q {prfQ})
\end{code}
\end{myhs}

  Note we parametrize |Kchain| by a relation |R|, over records. This enables us to
use the same datatype to talk about \emph{simple} and \emph{contiguous} $k$-chains 
--- where the rounds of of each block in the chain are contiguous.

\begin{myhs}
\begin{code}
Contig : Record -> Record -> Set
Contig r r' = round r' ≡ suc (round r)

Simple : Record -> Record -> Set
Simple _ _ = Unit

Kchain-contig : (k : Nat){r : Record} -> RecordChain r -> Set1
Kchain-contig = Kchain Contig
\end{code}
\end{myhs}

  Which brings us to the \emph{commit rule}. In LibraBFT, a block is
said to be commited if it is the start of a contiguous 3-chain.  We
encode this as a relation between record chains and blocks, by the
|CommitRule| datatype defined below.

\begin{myhs}
\begin{code}
data CommitRule : forall {r} -> RecordChain r -> Block -> Set1 where
  commitrule  : forall {r b}{rc : RecordChain r}(c3 : Kchain Contig 3 rc) 
              -> b == kchainBlock (suc (suc zero)) c3
              -> CommitRule rc b
\end{code}
\end{myhs}

  The |kchainBlock|, here, enables us to lookup a block from
the tail of the $k$-chain. Hence, the third block counting from
the end of a 3-chain is the \emph{head} of the chain.

\begin{myhs}
\begin{code}
kchainBlock : forall {k r R}{rc : RecordChain r} -> Fin k -> Kchain R k rc -> Block
kchainBlock zero     (schain {b = b}  _ _ _ _ _ _)   = b
kchainBlock (suc x)  (schain          _ _ _ _ _ ch)  = kchainBlock x ch
\end{code}
\end{myhs}

  We say that the commit rule is safe if given two blocks that match the commit 
rule, they belong to the same chain --- one chain extends the other.
This is estabilished by theorem S5 in the original paper.
In more detail, it states that if there exists a record chain |rc|, which
commits block |b| and a record chain |rc'|, which commits block |b'|, then
either |b| was already commited by |rc'| or |b'| was already commited
by |rc|. In other words, |rc| and |rc'| share a prefix.
We will encode theorem S5 and discuss its proof in more
detail in \Cref{sec:main-safety-theorem}.

  Membership in a record chain is encoded through
the |inRC| datatype. Its definition is similar to traditional list membership:

\begin{myhs}
\begin{code}
data inRCD (r0 : Record) : ∀{r1} -> RecordChain r1 -> Set where
  here   : ∀{rc : RecordChain r0} -> r0 inRC rc
  there  : ∀{r1 r2}{rc : RecordChain r1}(p : r1 EXT r₂)(pv : Valid rc r2)
         -> r0 inRC rc
         -> {prf : IsInPool r2}
         -> r0 inRC (step rc p pv {prf})
\end{code}
\end{myhs}

  
\subsubsection{Voting Constraints as State Invariants}
\label{sec:voting-constraints}

  Recall the typical round of LibraBFT, 
\Cref{fig:librabft-simplified-execution}. The leader 
broadcasts a block and the rest of the nodes vote on said block
if the block is \emph{valid}. In addition to block validity, 
honest nodes will only cast votes if the voting constraints are satisfied.
These constraints are put in place to ensure the safety of the commit
rule, which is, in fact, the main proof of our model.

  The LibraBFT protocol imposes three restrictions on which blocks
an honest participant is allowed to vote for. The first 
voting contraint is the \emph{increasing-round} constraint
and is presented in the original work~\cite{Baudet2019} as:

\begin{quote}
An honest node that voted once for a block |b| in the past may only vote for |b'|
if |round b < round b'|
\end{quote}

  At this point in our model, though, we have only modeled a snapshot
of a local honest participant's state at a single point in time
(|isRecordStoreState|).  Yet, the \emph{increasing-round} constraint
poses a difficulty. Any attempt to naively encode this constraint in a
model of a single local |RecordChain| will fail. The reason being the
informal use of temporal modalities such as ``has voted'' and ``may
only vote'' (in the future).  Squinting at the \emph{increasing-round}
constraint, though, we see that it imposes an invariant on
the states of a local copy: the order that an honest participant
has casted their votes is strictly increasing with respect to rounds.
To encode this, we proceed to add a |vOrder : Nat| field
to the |Vote| record to make this explicit in the model. This field is
distinguished in \Cref{fig:record-defs}.

  With an explicit |vOrder| field, the task of encoding the \emph{increasing-round}
constraint becomes much simpler. It states that if an honest participant |alpha|
has voted for two blocks, the round of these blocks is proportional to the
order in which |alpha| voted:

\begin{myhs}
\begin{code}
module Abstract {a}(RSS : Set a)(isRSS : isRecordStoreState RSS) where
  IncreasingRoundRule : Set1
  IncreasingRoundRule 
     = (alpha : Author ec) -> Honest alpha
     -> forall {q q'}(va  : alpha inQC q)(va' : alpha inQC q') -- alpha has voted for q and q'
     -> vOrder (inQCVote q va) < vOrder (inQCVote q' va')
     -> qRound (qBase q) < qRound (qBase q')
\end{code}
\end{myhs}

  There are different mechanisms one could use to ensure the
relationship between |vOrder| and rounds. One example is to actually
change the protocol and include |vOrder| directly in the network
messages. This would enable honest participants to keep a tally and
detect dishonest participants breaking this rule, increasing the
accountability of the system. Translating |vOrder| to an actual
implementation of LibraBFT is out of the scope of this paper, but the
important point is that it is the observational consequence of the
\emph{increasing-round} constraint and hence, a realistic piece of
explicit information to add to our abstract model.

  The second voting constraint states that an honest participant
may vote at most once per round. In our vocabulary, this means the
order field uniquely identifies the vote of an \emph{honest} participant.

\begin{myhs}
\begin{code}
module Abstract {a}(RSS : Set a)(isRSS : isRecordStoreState RSS) where
  VotesOnlyOnceRule : Set1
  VotesOnlyOnceRule 
     = (alpha : Author ec) -> Honest alpha
     -> forall {q q'}(va  : alpha inQC q)(va' : alpha inQC q') -- alpha has voted for q and q'
     -> vOrder (inQCVote q va) == vOrder (inQCVote q' va')
     -> inQCVote q va == inQCVote q' va'
\end{code}
\end{myhs}

  The third and final voting constraint -- named the |LockedRoundRule| -- is 
more intricate. It specifies a lower bound on the round
of blocks that can be extended by an honest participants vote.
The intuition behind this rule is for
honest participants to never \emph{revive} old forks of the state
by extending blocks that have been settled long in the past.

  The \emph{locked round} of an honest participant $\alpha$ is 
the highest round of the head of a $2$-chain ever known to $\alpha$,
or zero if $\alpha$ knows of no $2$-chain. This property, stated
as an invariant in terms of |vOrder| states that given that $\alpha$
knows of a $2$-chain, any vote isued by $\alpha$ \emph{after} its knowledge
of the $2$-chain, is for a block issued at a round bigger than $\alpha$'s
locked round. Note that the $2$-chain need not be contiguous.

\begin{myhs}
\begin{code}
module Abstract {a}(RSS : Set a)(isRSS : isRecordStoreState RSS) where
  LockedRoundRule : Set1
  LockedRoundRule
    = forall {Q}(alpha : Author ec) -> Honest alpha
    -> forall {q}{rc : RecordChain (Q q)}{n : Nat}(c2 : Kchain Q (2 + n) rc)
    -> (valpha : alpha inQC q) -- alpha knows of the 2-chain because it voted on the tail.
    -> ∀{q'}(rc' : RecordChain (Q q'))
    -> (valpha' : alpha inQC q')
    -> vOrder (inQCVote q valpha) < vOrder (inQCVote q' valpha')
    -> bRound (kchainBlock (suc zero) c2) <= prevRound rc'
\end{code}
\end{myhs}

  Besides the voting constraints, we need one last correctness invariant 
about record store states to separate the incorrect ones from the
correct ones. As suggested in \Cref{fig:recordstorestate}, every record
stored in the record pool must be part of a record chain. That is,
it must have been validated and must extend some chain. We can encode
this by requiring that one can always trace back a record chain from
any record in the pool.

\begin{myhs}
\begin{code}
module Abstract {a}(RSS : Set a)(isRSS : isRecordStoreState RSS) where
  Correct : Set1
  Correct = {r : Record} -> isInPool isRSS r -> RecordChain r
\end{code}
\end{myhs}

  
\subsubsection{Main Safety Theorem}
\label{sec:main-safety-theorem}

  With the correct vocabulary at hand, we are equipped to 
speak about the safety theorems and in which circumstances
they hold. We seek to prove that in a state where all the
invariants hold, a newly commited block can only
extend the chain containing the committed blocks.

  We start encoding a \emph{safe} record store state as
a record, which can later be passed around as (anonymous)
module parameter, similar to what we have been doing so far.

\begin{myhs}
\begin{code}
record SafeRSS {a}(RSS : Set a) : Set (suc a) where
  fields
    isRSS         : isRecordStoreState RSS

    correct       : Correct              isRSS
    incr-round    : IncreasingRoundRule  isRSS
    votes-once    : VotesOnlyOnceRule    isRSS
    locked-round  : LockedRoundRule      isRSS
\end{code}
\end{myhs}

  Finally, to prove that the constraints of the protocol 
imply that the commit rule is safe, it is sufficient
to inhabit the |thmS5| defined below.

\begin{myhs}
\begin{code}
module Abstract {a}(RSS : Set a)(safe : SafeRSS RSS) where
  thmS5  : forall {q q'}{rc : RecordChain (Q q)}{rc' : RecordChain (Q q')}
         -> {b b' : Block}
         -> CommitRule rc  b
         -> CommitRule rc' b'
         -> Either  HashBroke 
                    (Either (B b inRC rc') (B b' inRC rc)
\end{code}
\end{myhs}

  The proof of |thmS5| has been outlined in the original paper
and is unremarkable, given that three other important lemmas hold.
\victor{present the type of |lemmaS2|, |lemmaS3| and |propS4|} 

\subsection{Using the Abstract Model}
\label{sec:concrete-librabft}

  The purpose of the abstract model is to shave away unecessary detail
that is irrelevant to the main safety argument. Examples include
verification of signatures, detection of malformed messages,
detection of breakage of invariants. Moreover, our abstract model
states predicates about one snapshot of a participant state
instead of being concerned with the transitions that led to a particular state.
In this section, we explore how the abstract model can be used to
reason about a particular implementation.
The core of any implementation of LibraBFT will rely on three major parts;

\begin{enumerate}
  \item At the lowest level, one will have to model a network layer
        with operations such as send and receive providing certain guarantees.
        This presents modelling challanges in its own and is a separate
        effort from the work in this paper.

  \item On top of the network layer, one would implemented the logic
        layer of the protocol. This is where we can analyze received
        messages and issue actions that work on the state or the enviroment.
        The available actions might include network actions, 
        for example \emph{issue-timeout} or \emph{broadcast-block},
        but it will also inclue local actions, such as \emph{validate-network-record},
        or \emph{insert-valid-record}.

  \item Finally, one would implement the denotational semantics of the
        possible actions with respect to a particular state type.
        Any sane implementation would restrict the means by which
        this state can be updated. In here, we will assume that the only
        way to update a state is through \emph{insert-valid-record}.
\end{enumerate}

\begin{figure}
\centering
\victor{finish this drawing too... what to include?}
\begin{tikzpicture}[
   interact/.style={ cloud , draw
                   , cloud puffs=9.7982 
                   , cloud puff arc=120, aspect=2, inner ysep=0.2em}
 , node distance = 2.4cm
 ]
\node                    (empty)    {|empty|};
\node [right = 3cm of empty] (absempty) {$\emptyset$};
\draw [->] (empty) -- (absempty) node [midway, above] {|abstractRSS|};

\node [below = of empty] (st1)  {|st1|};
\node [right = 3cm of st1]   (abs1) {$\{ r_1 \}$};
\draw [->] (st1) -- (abs1) node [midway, above] {|abstractRSS|};
\draw [->,dashed] (empty) -- (st1) node [midway,right] {|insert r1|};

\node [below = of st1] (st2)  {|st2|};
\node [right = 3cm of st2] (abs2) {$\{ r_1 , r_2 \}$};
\draw [->] (st2) -- (abs2) node [midway, above] {|abstractRSS|};
\draw [->,dashed] (st1) -- (st2) node [midway,right] {|insert r2|};

\node [interact] at ($ (empty)!0.5!(st1) - (2,0) $) (int1) {interact};
\draw [->] (empty) to[out=180, in=90]  ($ (int1.north) + (0,0.1) $);
\draw [->] ($ (int1.south) - (0,0.1) $) to[out=270, in=180] (st1);

\node [interact] at ($ (st1)!0.5!(st2)   - (2,0) $) (int2) {interact};
\draw [->] (st1) to[out=180, in=90]  ($ (int2.north) + (0,0.1) $);
\draw [->] ($ (int2.south) - (0,0.1) $) to[out=270, in=180] (st2);

\node at ($ (absempty) + (-0.5, 0.5) $) (absfitstart) {};
\node at ($ (abs2)     - (-0.5, 0.5) $) (absfitend) {};
\node [fit = (absfitstart) (absfitend) , draw , rounded corners=2mm , dotted] 
  (absbox) {};

\node at (absbox.north) [below, inner sep=1mm] 
  {|Abstract|}; 

\end{tikzpicture}
\caption{Diagram of the relationship between the different layers}
\label{fig:concrete-diagram}
\end{figure}

  These layers are illustrated in \Cref{fig:concrete-diagram}, where we
see that the initial state is fed to an interaction layer, which will
send, receive and analize messages, eventually transitioning to a new state, |st1|.
This new state should be the result of the evaluation of an
\emph{insert-valid-record} action. The abstract view over each state is
only concerned with the set of records in the state at a given time.

  Now, say we want to prove that |st2|, as in \Cref{fig:concrete-diagram} enjoys 
the main safety property, that is, commited records are in the same chain. 
Given that |abstractRSS| is sound -- does not forget or insert any records --
all we have to do is use the fact that the empty state |empty| enjoyed the main safety
property and the fact that the |insert| function respects all the invariants.
This means that |abstractRSS st2| respects all invariants. The whole proof, in
pseudo-Agda, would look something like the following.

\begin{myhs}
\begin{code}

committed : ConcreteRSS -> Block -> Set
committed rss b = b `elem` rss TIMES (exists (rc) (CommitRule rc b))
  where
    open import Abstract.RecordChain rss abstractRSS dots

st2 : ConcreteRSS
st2 = insert r2 (insert r1 empty)

st2IsSafe  : {b b' : Block}
           -> committed st2 b
           -> committed st2 b'
           -> Either  HashBroke (Either (B b EXTTR B b') (B b' EXTTR B b)
st2IsSafe (binst2 , (rcb , commb)) (b'inst2 , (rcb' , commb'))
  = map (either inRC_to_EXTTR inRC_to_EXTTR) <$$> thm5 commb commb'
 where
   safe_st2 = insert_respects_safe r2 (insert_respects_safe r1 empty_safe)

   open import Abstract.RecordChain.Properties st2 abstractRSS safe_st2
\end{code}
\end{myhs}

  Implementing of the concrete layer will rely on,
amongst other things, the implementation of the insertion
function that manipulates the state. In fact, this is the only function
that should yield an observable difference in abstract states.
That is, |abstractRSS (insert r1 st) /= abstractRSS st|, whereas
|abstractRSS (broadcast r1 st) == abstractRSS st|.

  The concrete states, |ConcreteRSS|, will generally consist in
a list of authorized authors for the current epoch and a mutable part,
which will contain something like a hashmap for the records in store.
For example, the records below could make the base for implementing
an insertion function.

\begin{myhs}
\begin{code}
record ConcreteRSS : Set where
  field
    rssEpochId    : EpochId
    rssEpochConf  : ConcreteEpochConf                     -- public keys; authors; ...
    rssMutable    : ConcreteMutRSS (Author rssEpochConf)  -- mutable part

record ConcreteMutRSS (authors : Set) : Set where
  field
    rssRound        : Nat
    rssLockedRound  : Nat           -- what's my locked round?
    rssLastVote     : Vote authors  -- what's my last vote?
    rssBlocks       : HashMap BlocKHash  (Block  authors)
    rssQCs          : HashMap QCHash     (QC     authors)
    dots
\end{code}
\end{myhs}

\victor{I'm here. The pieces below might change. In fact; the |abstractRSS| might change.
As I was writing this I started realizing that we will have to find an equality
notion for |isRecordStoreState a|. Otherwise, we can't prove that the |abstractRSS|
function is sound. This equality will probably look like a bisimilarity, but I
haven't thought too much about it yet. I will think about this for a while next week.}

  The abstract view of a concrete state is defined as a function
that proces that any specific value |rss| or type |ConcreteRSS| satisfies
the |isRecordStoreState| ``interface''.

\begin{myhs}
\begin{code}
abstractRSS : (rss : ConcreteRSS)
            -> isRecordStoreState (ConcreteMutRSS (Author (rssEpochConf rss)))
\end{code}
\end{myhs}

  The |abstractRSS| function is very important since it enables us to instantiate
the invariants for specific concrete states.

\begin{myhs}
\begin{code}
ConcreteValidRSS : RecordStoreState -> Set1
ConcreteValidRSS rss = Abstract.Valid (abstractRSS rss)

ConcreteLockedRound : RecordStoreState -> Set1
ConcreteLockedRound rss = Abstract.LockedRoundRule (abstractRSS rss)

dots
\end{code}
\end{myhs}

  

