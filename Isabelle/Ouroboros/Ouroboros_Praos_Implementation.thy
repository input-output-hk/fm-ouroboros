section \<open> Implementation of the Ouroboros Praos protocol \<close>

theory Ouroboros_Praos_Implementation
  imports
    Chi_Calculus.Typed_Basic_Transition_System
    "HOL-Library.BNF_Corec"
    Complex_Main
begin

subsection \<open> Introduction \<close>

text \<open>
  In this section we present an implementation of the Ouroboros Praos protocol as defined in
  @{cite praos}. Since a security analysis of the protocol is out of scope, we do not model the
  environment \<open>\<Z>\<close>, the adversary \<open>\<A>\<close>, etc. However, we retain the use of the Universal
  Composability (UC) framework for the sake of design modularity.
\<close>

subsection \<open> Preliminaries \<close>

text \<open>
  We let \<open>v \<bar>\<bar> w\<close> denote concatenation of ``strings'' (i.e. arbitrary values):
\<close>

abbreviation concat :: "'a \<Rightarrow> 'b \<Rightarrow> 'a \<times> 'b" (infixr \<open>\<bar>\<bar>\<close> 65) where
  "v \<bar>\<bar> w \<equiv> (v, w)"

text \<open>
  Public-key cryptography depends on a pair of a secret key and a verification key:
\<close>

typedecl secret_key

typedecl verification_key

subsubsection \<open> The Semi-Synchronous model \<close>

text \<open>
  \label{sec:semi-sync-model-ref}
  In the paper, a semi-synchronous model with an upper bound \<open>\<Delta>\<close> in message delay is used. Regarding
  \<open>\<Delta>\<close>, we stress that the protocol is oblivious of \<open>\<Delta>\<close> and this bound is only used in the security
  analysis. Hence from the protocol's point of view the network is no better than an eventual
  delivery network (without a concrete bound), which can be modeled using our process calculus using
  for example a reliable broadcasting server process.
  Regarding synchrony, we simply assume that an external ``clock process'' signals each stakeholder
  when a round (i.e. slot) ends, and that messages sent in one round are received at the onset of
  the next round.
\<close>

paragraph \<open> Time and slots. \<close>

text \<open>
  We define the concepts of epoch and slot. As defined in the paper, slots and epochs begin at 1:
\<close>

type_synonym epoch = nat

type_synonym slot = nat

abbreviation first_slot :: slot where
  "first_slot \<equiv> 1"

abbreviation first_epoch :: epoch where
  "first_epoch \<equiv> 1"

paragraph \<open> The Delayed Diffuse Functionality. \<close>

text \<open>
  We do not model the network as a separate ideal functionality \textsf{DDiffuse}\<open>\<^sub>\<Delta>\<close> but rely on
  our process calculus features for communication. In particular, a single channel is used both to
  read the received messages from a stakeholder's ``incoming string'' (or ``mailbox'') and to
  ``diffuse'' a message. Also, the restriction that a stakeholder is allowed to diffuse once in a
  round is explicitly enforced by the stakeholder process implementation, see Section
  \ref{sec:sh-process-ref}.
\<close>

paragraph \<open> Random Oracle. \<close>

text \<open>
  We will simply assume that we can compute the hash value of any value:
\<close>

typedecl hash \<comment> \<open> Hash values (i.e. $\{0,1\}^w$ in the paper) \<close>

axiomatization
  where
    hash_finite: "OFCLASS(hash, finite_class)"
  and
    hash_equal: "OFCLASS(hash, equal_class)"

instance hash :: finite
  by (rule hash_finite)

instance hash :: equal
  by (rule hash_equal)

consts \<H> :: "'a \<Rightarrow> hash" \<comment> \<open> A collision-resistant hash function \<close>

text \<open>
  with no way of recovering @{typ 'a} from @{type hash}.
\<close>

subsection \<open> The Full Protocol \<close>

text \<open>
  We only implement the protocol that handles the dynamic case (i.e. $\pi_{\mathrm{DPoS}}$), since
  the static case is used as the base case in the ``inductive'' security proof.
\<close>

subsubsection \<open> Protocol parameters \<close>

text \<open>
  The protocol's implementation depends on a number of parameters. In this section we define such
  parameters.
\<close>

text \<open>
  \<^item> A transaction is declared stable if it is in a block more than \<open>k\<close> blocks deep in the ledger:
\<close>

consts k :: nat

text \<open>
  \<^item> The length \<open>R\<close> of an epoch, measured in slots:
\<close>

consts R :: nat

text \<open>
  \<^item> The active slot coefficient $f \in (0, 1]$. Establishes the probability that at least one
    stakeholder is elected as a slot leader, that is, the probability that a slot is not empty:
\<close>

consts f :: real

text \<open>
  \<^item> Two special, but arbitrary, values that we use when calling the VRF in slot leader selection
    ($\mathtt{TEST}$) and block nonce creation/validation ($\mathtt{NONCE}$). They are used to
    provide domain separation:
\<close>

datatype vrf_query_type = TEST | NONCE

subsubsection \<open> Ideal functionalities \<close>

text \<open>
  In the paper, the protocol is described with respect to ideal functionalities. In this section we
  model the functionalities available to our protocol implementation. For the sake of simplicity,
  we do not model the key generation algorithms for \<open>\<F>\<close>$_{\mathsf{VRF}}$, \<open>\<F>\<close>$_{\mathsf{KES}}$ and
  \<open>\<F>\<close>$_{\mathsf{DSIG}}$ but these keys are given as parameters to each stakeholder.
\<close>

paragraph \<open> Functionality \<open>\<F>\<close>$_{\mathsf{VRF}}$. \<close>

text \<open>
  We model the evaluation of a VRF as a function that, given an input value and a secret key,
  produces a random value and a proof:
\<close>

typedecl vrf_output

typedecl vrf_proof

axiomatization
  where
    vrf_output_finite: "OFCLASS(vrf_output, finite_class)"
  and
    vrf_proof_finite: "OFCLASS(vrf_proof, finite_class)"

instance vrf_output :: finite
  by (rule vrf_output_finite)

instance vrf_proof :: finite
  by (rule vrf_proof_finite)

type_synonym vrf_value = "vrf_output \<times> vrf_proof"

consts vrf_output_size :: nat (\<open>l\<^sub>V\<^sub>R\<^sub>F\<close>)

consts evaluate_vrf :: "secret_key \<Rightarrow> 'a \<Rightarrow> vrf_value"

text \<open>
  Also, we can verify that a particular random value was produced correctly:
\<close>

consts verify_vrf :: "verification_key \<Rightarrow> 'a \<Rightarrow> vrf_value \<Rightarrow> bool"

text \<open>
  Finally, we can cast a VRF output into a real number:
\<close>

consts vrf_output_to_real :: "vrf_output \<Rightarrow> real"

paragraph \<open> Functionalities \<open>\<F>\<close>$_{\mathsf{KES}}$ and \<open>\<F>\<close>$_{\mathsf{DSIG}}$. \<close>

text \<open>
  In the paper, the functionality \<open>\<F>\<close>$_{\mathsf{DSIG}}$ models a regular digital signature scheme
  which is used to sign transactions. Also, the functionality \<open>\<F>\<close>$_{\mathsf{KES}}$ adds the
  capability of allowing the signing key to ``evolve'' in such a way that the adversary
  cannot forge past signatures, and is used to sign blocks. Therefore, we model these two
  functionalities as a single, ordinary digital signature scheme. With this scheme, we can sign a
  value using a secret key:
\<close>

typedecl signature

axiomatization
  where
    signature_finite: "OFCLASS(signature, finite_class)"

instance signature :: finite
  by (rule signature_finite)

consts sign :: "secret_key \<Rightarrow> 'a \<Rightarrow> signature"

text \<open>
  and verify that a value is properly signed using a verification key:
\<close>

consts verify :: "verification_key \<Rightarrow> 'a \<Rightarrow> signature \<Rightarrow> bool"

paragraph \<open> Functionality \<open>\<F>\<close>$^{\tau,r}_{RLB}$. \<close>

text \<open>
  In the paper, the functionality \<open>\<F>\<close>$^{\tau,r}_{RLB}$ models a randomness beacon that basically
  provides a fresh nonce for each epoch to (re)seed the election process. Also, this beacon is
  resettable and leaky in order to strengthen the adversary, which we evidently ignore. Finally,
  the beacon (via \<open>\<F>\<close>$_{\mathsf{INIT}}$) provides the stakeholders with the genesis block; instead
  our implementation passes the genesis block as a parameter to each stakeholder.
\<close>

typedecl nonce

consts new_epoch_rnd :: nonce

subsubsection \<open> Basic definitions \<close>

text \<open>
  In this section we introduce basic definitions for the protocol.
\<close>

paragraph \<open> Stake Distribution. \<close>

text \<open>
  A stake distribution is simply a map from stakeholder labels \<open>U\<^sub>i\<close> to their respectives stakes \<open>s\<^sub>i\<close>:
\<close>

type_synonym stakeholder_id = nat

type_synonym stake = nat

type_synonym stake_distr = "stakeholder_id \<rightharpoonup> stake"

paragraph \<open> Genesis block. \<close>

text \<open>
  As defined in the paper, we have a genesis block associated to a blockchain:
\<close>

type_synonym stakeholder_keys = "
  verification_key \<times> \<comment> \<open> $v^\\mathrm{vrf}$ \<close>
  verification_key \<times> \<comment> \<open> $v^\\mathrm{kes}$ \<close>
  verification_key" \<comment> \<open> $v^\mathrm{dsig}$ \<close>

type_synonym genesis = "
  (stakeholder_id \<rightharpoonup> stakeholder_keys) \<times> \<comment> \<open> stakeholders' verification keys \<close>
  stake_distr \<times> \<comment> \<open> initial stake distribution $\\mathbb{S}_0$ \<close>
  nonce" \<comment> \<open> initial nonce \<open>\<eta>\<^sub>0\<close> \<close>

paragraph \<open> Transactions. \<close>

text \<open>
  In the paper, the environment \<open>\<Z>\<close> issues transactions on behalf of any stakeholder \<open>U\<^sub>i\<close> by
  requesting a signature on the transaction and handing the transaction data $d \in \{0,1\}^*$ to
  stakeholders to put them into blocks. We decide not to model transaction processing this way but
  use a more realistic approach instead: Transactions are assumed to be received by stakeholders
  through the network. A transaction body is assumed to be a simple assertion of the form
  ``Stakeholder \<open>U\<^sub>i\<close> transfers stake \<open>s\<close> to Stakeholder \<open>U\<^sub>j\<close>'':
\<close>

type_synonym transaction_body = "
  stakeholder_id \<times> \<comment> \<open> \<open>U\<^sub>i\<close> \<close>
  stakeholder_id \<times> \<comment> \<open> \<open>U\<^sub>j\<close> \<close>
  stake \<comment> \<open> \<open>s\<close> \<close>"

text \<open>
  and a transaction consists of a transaction body accompanied by a signature of it under the
  signing key corresponding to \<open>U\<^sub>i\<close>:
\<close>

type_synonym transaction = "transaction_body \<times> signature"

text \<open>
  We can apply a transaction to a stake distribution. The paper does not define how this is done,
  so we use the intuitive definition and assume that the source and target stakeholders exist in the
  stake distribution and that the source stakeholder has enough stake for the withdrawal:
\<close>

fun apply_transaction :: "transaction \<Rightarrow> stake_distr \<Rightarrow> stake_distr" where
  "apply_transaction ((U\<^sub>i, U\<^sub>j, s), _) \<S> = \<S>(U\<^sub>i \<mapsto> the (\<S> U\<^sub>i) - s, U\<^sub>j \<mapsto> the (\<S> U\<^sub>j) + s)"

paragraph \<open> Block. \<close>

text \<open>
  We define a block proof, denoted by \<open>B\<^sub>\<pi> = (U\<^sub>i, y, \<pi>)\<close> in the paper:
\<close>

type_synonym block_proof = "
  stakeholder_id \<times> \<comment> \<open> Stakeholder who created the block \<close>
  vrf_value" \<comment> \<open> VRF value used for slot leader selection \<close>

text \<open>
  \label{sec:block-ref}
  and we distinguish between an \<open>unsigned block\<close> (a block without a signature, a concept not
  explicitly present in the paper) and a signed block. Since the latter corresponds to the concept
  of a block in the paper, we refer to a signed block as simply a \<open>block\<close>. For the sake of
  completeness, we include the nonce proof in a block (denoted by $\rho = (\rho_y, \rho_\pi)$ in the
  paper), despite this datum is actually used by the protocol $\pi_{RLB}$ and not by our protocol
  implementation:
\<close>

type_synonym unsigned_block = "
  slot \<times> \<comment> \<open> Slot when the block was created \<close>
  hash option \<times> \<comment> \<open> Previous block hash (if any), denoted by \<open>st\<close> in the paper \<close>
  transaction list \<times> \<comment> \<open> Transaction data, denoted by \<open>d\<close> in the paper \<close>
  block_proof \<times> \<comment> \<open> Block proof (proof of leadership), denoted by \<open>B\<^sub>\<pi>\<close> in the paper \<close>
  vrf_value" \<comment> \<open> Nonce proof \<close>

type_synonym block = "unsigned_block \<times> signature"

fun bl_slot :: "block \<Rightarrow> slot" where
  "bl_slot ((sl, _, _, _), _) = sl"

fun bl_txs :: "block \<Rightarrow> transaction list" where
  "bl_txs ((_, _, d, _), _) = d"

text \<open>
  We can apply a block to a stake distribution by applying all transactions in the block to the
  stake distribution:
\<close>

abbreviation apply_block :: "block \<Rightarrow> stake_distr \<Rightarrow> stake_distr" where
  "apply_block B \<S> \<equiv> fold apply_transaction (bl_txs B) \<S>"

paragraph \<open> Blockchain. \<close>

text \<open>
  A blockchain is simply a sequence of blocks. We do not record the genesis block explicitly as
  part of the blockchain: 
\<close>

type_synonym blockchain = "block list"

text \<open>
  We define a function to prune the last \<open>m\<close> blocks in a blockchain \<open>\<C>\<close>, denoted by \<open>\<C>\<^bsup>\<lceil>m\<^esup>\<close> in the
  paper:
\<close>

abbreviation prune_chain :: "blockchain \<Rightarrow> nat \<Rightarrow> blockchain" (infixl \<open>\<lceil>\<close> 999) where
  "\<C> \<lceil>m \<equiv> take (length \<C> - m) \<C>"

text \<open>
  and a function to prune the blocks in a blockchain which have slots greater than a given slot:
\<close>

abbreviation prune_after :: "slot \<Rightarrow> blockchain \<Rightarrow> blockchain" where
  "prune_after sl \<C> \<equiv> takeWhile (\<lambda>B. bl_slot B \<le> sl) \<C>"

text \<open>
  We let \<open>\<C>\<^sub>1 \<preceq> \<C>\<^sub>2\<close> indicate that the blockchain \<open>\<C>\<^sub>1\<close> is a prefix of the blockchain \<open>\<C>\<^sub>2\<close>:
\<close>

abbreviation is_prefix_of :: "blockchain \<Rightarrow> blockchain \<Rightarrow> bool" (infixl \<open>\<preceq>\<close> 50) where
  "\<C>\<^sub>1 \<preceq> \<C>\<^sub>2 \<equiv> \<exists>m. \<C>\<^sub>2 \<lceil>m = \<C>\<^sub>1"

text \<open>
  And we can apply a blockchain \<open>\<C>\<close> to a stake distribution \<open>\<S>\<close> by sequentially applying all blocks
  in \<open>\<C>\<close> to \<open>\<S>\<close>:
\<close>

abbreviation apply_blockchain :: "blockchain \<Rightarrow> stake_distr \<Rightarrow> stake_distr" where
  "apply_blockchain \<C> \<S> \<equiv> fold apply_block \<C> \<S>"

paragraph \<open> Absolute and Relative Stake. \<close>

text \<open>
  The paper defines the (somewhat vague) concepts of @{emph \<open>maximum\<close>} and @{emph \<open>minimum\<close>}
  absolute stake controlled by a set of parties, as well as the concepts of
  @{emph \<open>adversarial stake ratio\<close>} and @{emph \<open>honest stake ratio\<close>}. However, for our
  implementation we only need the absolute @{emph \<open>maximum\<close>} stake controlled by @{emph \<open>all\<close>}
  stakeholders, denoted by \<open>s\<^sup>+(\<S>)\<close> where \<open>\<S>\<close> is an arbitrary stake distribution:
\<close>

abbreviation absolute_stake :: "stake_distr \<Rightarrow> stake" (\<open>s\<^sup>+'(_')\<close>) where
  "s\<^sup>+(\<S>) \<equiv> \<Sum>U\<^sub>j \<in> dom \<S>. the (\<S> U\<^sub>j)"

text \<open>
  and the relative stake controlled by @{emph \<open>a single\<close>} stakeholder \<open>U\<^sub>i\<close>, taken as
  @{emph \<open>maximum\<close>} across of the view of @{emph \<open>all\<close>} stakeholders w.r.t. a stake distribution
  \<open>\<S>\<close>, denoted by \<open>\<alpha>\<^sup>+(U\<^sub>i, \<S>)\<close>. For this definition we assume that \<open>U\<^sub>i\<close> exists in \<open>\<S>\<close>:
\<close>

type_synonym relative_stake = real

abbreviation
  relative_stake_of :: "stakeholder_id \<Rightarrow> stake_distr \<Rightarrow> relative_stake" (\<open>\<alpha>\<^sup>+'(_,_')\<close>)
where
  "\<alpha>\<^sup>+(U\<^sub>i, \<S>) \<equiv>
    let
      s\<^sub>i = the (\<S> U\<^sub>i);
      s\<^sub>\<P> = s\<^sup>+(\<S>)
    in
      s\<^sub>i / s\<^sub>\<P>"

subsubsection \<open> Leader election \<close>

text \<open>
  In this section we model the staking procedure which is used for the slot leader to compute and
  send the next block. We define the probability \<open>\<phi>(\<alpha>)\<close> that a stakeholder with relative stake \<open>\<alpha>\<close>
  is elected as a slot leader:
\<close>

abbreviation slot_leader_probability :: "relative_stake \<Rightarrow> real" (\<open>\<phi>'(_')\<close>) where
  "\<phi>(\<alpha>) \<equiv> 1 - (1 - f) powr \<alpha>"

text \<open>
  Next, given epoch \<open>j\<close>, genesis block \<open>G\<close> and blockchain \<open>\<C>\<close>, we define a function \<open>\<S>(j, G, \<C>)\<close>
  that computes the stake distribution at the end of epoch \<open>j - 2\<close> as reflected in \<open>\<C>\<close> if \<open>j \<ge> 2\<close>;
  otherwise returns the initial stake distribution in \<open>G\<close>:
\<close>

fun epoch_stake_distr :: "epoch \<Rightarrow> genesis \<Rightarrow> blockchain \<Rightarrow> stake_distr" (\<open>\<S>'(_,_,_')\<close>) where
  "\<S>(Suc 0, (_, \<S>\<^sub>0, _), _) = \<S>\<^sub>0" |
  "\<S>(j, (_, \<S>\<^sub>0, _), \<C>) = (
    let
      sl\<^sub>e\<^sub>n\<^sub>d = (j - 2) * R;
      \<C>' = prune_after sl\<^sub>e\<^sub>n\<^sub>d \<C>
    in
      apply_blockchain \<C>' \<S>\<^sub>0)"

text \<open>
  Now, given a genesis block \<open>G\<close> and a blockchain \<open>\<C>\<close>, a stakeholder \<open>U\<^sub>i\<close> is an eligible slot leader
  for a particular slot in an epoch \<open>j\<close> if its VRF output is smaller than a threshold value, denoted
  by \<open>T(U\<^sub>i, j, G, \<C>)\<close>, and defined as follows:
\<close>

abbreviation slot_leader_threshold :: "
     stakeholder_id
  \<Rightarrow> epoch
  \<Rightarrow> genesis
  \<Rightarrow> blockchain
  \<Rightarrow> real"
  (\<open>T'(_,_,_,_')\<close>)
where
  "T(U\<^sub>i, j, G, \<C>) \<equiv>
    let
      \<S>\<^sub>j = \<S>(j, G, \<C>);
      \<alpha> = \<alpha>\<^sup>+(U\<^sub>i, \<S>\<^sub>j) 
    in
      2 ^ l\<^sub>V\<^sub>R\<^sub>F * \<phi>(\<alpha>)"

text \<open>
  Finally, a stakeholder can ask if they are a slot leader for a given slot (note that stakeholders
  can only check this for themselves, not for other stakeholders):
\<close>

abbreviation is_slot_leader :: "slot \<Rightarrow> secret_key \<Rightarrow> nonce \<Rightarrow> real \<Rightarrow> vrf_value option" where
  "is_slot_leader sl sk \<eta> T \<equiv>
    let
      (y, \<pi>) = evaluate_vrf sk (\<eta> \<bar>\<bar> sl \<bar>\<bar> TEST)
    in
      if vrf_output_to_real y < T then Some (y, \<pi>) else None"

subsubsection \<open> Auxiliary functions \<close>

text \<open>
  We can compute the epoch to which a given slot belongs:
\<close>

abbreviation slot_epoch :: "slot \<Rightarrow> epoch" where
  "slot_epoch sl \<equiv> nat \<lceil>sl / R\<rceil>"

text \<open>
  and check whether a given slot is the first one in its epoch:
\<close>

abbreviation first_in_epoch :: "slot \<Rightarrow> bool" where
  "first_in_epoch sl \<equiv> R dvd (sl - 1)"

subsubsection \<open> Verification \<close>

text \<open>
  We can verify that a transaction is valid w.r.t. a genesis block, namely that the source and
  target stakeholders exist in the genesis block's stake distribution, that the source stakeholder
  has enough stake for the withdrawal, and that the signature is valid. Here we assume that the
  given genesis block is well-formed, in particular that the domain of both maps coincide:
\<close>

abbreviation verify_tx :: "transaction \<Rightarrow> genesis \<Rightarrow> bool" where
  "verify_tx tx G \<equiv>
    let
      (txbody, \<sigma>) = tx;
      (U\<^sub>i, U\<^sub>j, s) = txbody;
      (vks, \<S>\<^sub>0, _) = G;
      (_, _, vk\<^sub>i) = the (vks U\<^sub>i) \<comment> \<open>\<open>U\<^sub>i\<close>'s DSIG verification key\<close>
    in
      \<exists>s\<^sub>i s\<^sub>j. \<S>\<^sub>0 U\<^sub>i = Some s\<^sub>i \<and> \<S>\<^sub>0 U\<^sub>j = Some s\<^sub>j \<and> s\<^sub>i \<ge> s \<and> verify vk\<^sub>i txbody \<sigma>"

text \<open>
  and thus we can trivially verify whether a list of transactions is valid w.r.t. a genesis block:
\<close>

abbreviation verify_tx_data :: "transaction list \<Rightarrow> genesis \<Rightarrow> bool" where
  "verify_tx_data txs G \<equiv> \<forall>i \<in> {0..<length txs}. verify_tx (txs ! i) G"

text \<open>
  A key component of block verification is verifying the block proof, i.e. that the stakeholder who
  created the block was in the slot leader set of the slot in which the block was created:
\<close>

abbreviation
  verify_block_proof :: "slot \<Rightarrow> verification_key \<Rightarrow> nonce \<Rightarrow> vrf_value \<Rightarrow> real \<Rightarrow> bool"
where
  "verify_block_proof sl vk \<eta> v T \<equiv>
    verify_vrf vk (\<eta> \<bar>\<bar> sl \<bar>\<bar> TEST) v \<and> vrf_output_to_real (fst v) < T"

text \<open>
  Although the block nonce is not used (as explained in Section \ref{sec:block-ref}), we verify that
  it was properly created nonetheless:
\<close>

abbreviation verify_block_nonce :: "slot \<Rightarrow> verification_key \<Rightarrow> nonce \<Rightarrow> vrf_value \<Rightarrow> bool" where
  "verify_block_nonce sl vk \<eta> v \<equiv> verify_vrf vk (\<eta> \<bar>\<bar> sl \<bar>\<bar> NONCE) v"

text \<open>
  Armed with these definitions, we can now verify that a block is indeed valid:
\<close>

abbreviation verify_block :: "block \<Rightarrow> hash option \<Rightarrow> genesis \<Rightarrow> nonce \<Rightarrow> real \<Rightarrow> bool" where
  "verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v G \<eta> T \<equiv>
    let
      ((sl, st, d, B\<^sub>\<pi>, \<rho>), \<sigma>) = B;
      (U\<^sub>s, y, \<pi>) = B\<^sub>\<pi>;
      (\<rho>\<^sub>y, \<rho>\<^sub>\<pi>) = \<rho>
    in
      verify_tx_data d G \<and> (
      \<exists>v\<^sub>v\<^sub>r\<^sub>f v\<^sub>k\<^sub>e\<^sub>s v\<^sub>d\<^sub>s\<^sub>i\<^sub>g.
        Some (v\<^sub>v\<^sub>r\<^sub>f, v\<^sub>k\<^sub>e\<^sub>s, v\<^sub>d\<^sub>s\<^sub>i\<^sub>g) = (fst G) U\<^sub>s \<and> \<comment> \<open> \<open>U\<^sub>s\<close>'s verification keys \<close>
        verify_block_proof sl v\<^sub>v\<^sub>r\<^sub>f \<eta> (y, \<pi>) T \<and>
        verify_block_nonce sl v\<^sub>v\<^sub>r\<^sub>f \<eta> (\<rho>\<^sub>y, \<rho>\<^sub>\<pi>) \<and>
        verify v\<^sub>k\<^sub>e\<^sub>s (sl, st, d, B\<^sub>\<pi>, \<rho>) \<sigma>) \<and> (
      case oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v of
        None \<Rightarrow> True
      | Some h\<^sub>p\<^sub>r\<^sub>e\<^sub>v \<Rightarrow> the st = h\<^sub>p\<^sub>r\<^sub>e\<^sub>v)" \<comment> \<open> if \<open>oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v\<close> is not \<open>None\<close> then \<open>st\<close> is not \<open>None\<close> either \<close>

text \<open>
  and we can verify that a blockchain is indeed valid:
\<close>

abbreviation verify_chain :: "blockchain \<Rightarrow> genesis \<Rightarrow> nonce \<Rightarrow> bool" where
  "verify_chain \<C> G \<eta> \<equiv> \<forall>i \<in> {0..<length \<C>}.
    let
      B = \<C> ! i; \<comment> \<open> current block \<close>
      ((sl, _, _, B\<^sub>\<pi>, _), _) = B;
      U\<^sub>s = fst B\<^sub>\<pi>;
      oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v = if i = 0 then None else fst (snd (fst (\<C> ! (i - 1)))); \<comment> \<open> previous block hash \<close>
      T\<^sub>s = T(U\<^sub>s, slot_epoch sl, G, \<C>)
    in
      verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v G \<eta> T\<^sub>s"

subsubsection \<open> Stakeholder state \<close>

text \<open>
  Each stakeholder has access to its own state. We bundle the items comprising the stakeholder state
  in a record type:
\<close>

record stakeholder_state =
  ss_id :: stakeholder_id \<comment> \<open> ID of the stakeholder in the set \<open>U\<^sub>1, ..., U\<^sub>n\<close> \<close>
  ss_G :: genesis \<comment> \<open> genesis block \<close>
  ss_\<C> :: blockchain \<comment> \<open> current blockchain \<close>
  ss_\<eta> :: nonce \<comment> \<open> current epoch nonce \<open>\<eta>\<^sub>j\<close> \<close>
  ss_\<CC> :: "blockchain list" \<comment> \<open> blockchains received during the current slot \<close>
  ss_txs :: "transaction list" \<comment> \<open> transactions received during the current slot \<close>
  ss_st :: "hash option" \<comment> \<open> current state, namely the hash of the head of \<open>ss_\<C>\<close> \<close>
  ss_sk\<^sub>v\<^sub>r\<^sub>f :: secret_key \<comment> \<open> secret key for \<open>\<F>\<close>$_{\mathsf{VRF}}$ \<close>
  ss_sk\<^sub>k\<^sub>e\<^sub>s :: secret_key \<comment> \<open> secret key for \<open>\<F>\<close>$_{\mathsf{KES}}$ \<close>
  ss_sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g :: secret_key \<comment> \<open> secret key for \<open>\<F>\<close>$_{\mathsf{DSIG}}$ \<close>

text \<open>
  We can specify what the initial state for each stakeholder should be:
\<close>

abbreviation init_stakeholder_state :: "
     stakeholder_id
  \<Rightarrow> genesis
  \<Rightarrow> secret_key
  \<Rightarrow> secret_key
  \<Rightarrow> secret_key
  \<Rightarrow> stakeholder_state"
where
  "init_stakeholder_state U\<^sub>i G sk\<^sub>v\<^sub>r\<^sub>f sk\<^sub>k\<^sub>e\<^sub>s sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g \<equiv>
    let
      (_, _, \<eta>\<^sub>0) = G
    in
      \<lparr>
        ss_id = U\<^sub>i,
        ss_G = G,
        ss_\<C> = [],
        ss_\<eta> = \<eta>\<^sub>0,
        ss_\<CC> = [],
        ss_txs = [],
        ss_st = None,
        ss_sk\<^sub>v\<^sub>r\<^sub>f = sk\<^sub>v\<^sub>r\<^sub>f,
        ss_sk\<^sub>k\<^sub>e\<^sub>s = sk\<^sub>k\<^sub>e\<^sub>s,
        ss_sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g = sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g
      \<rparr>"

subsubsection \<open> Blockchain update \<close>

text \<open>
  In this section we model the procedure by which a stakeholder decides which blockchain to adopt
  given a set of alternatives received over the network in the current round (the ``longest chain''
  rule). We can check whether a blockchain forks from another at most \<open>m\<close> blocks:
\<close>

abbreviation forks_at_most :: "nat \<Rightarrow> blockchain \<Rightarrow> blockchain \<Rightarrow> bool" where
  "forks_at_most n \<C> \<C>' \<equiv>
    if
      \<exists>i. \<H> (\<C> ! i) \<noteq> \<H> (\<C>' ! i)
    then
      length (drop (LEAST i. \<H> (\<C> ! i) \<noteq> \<H> (\<C>' ! i)) \<C>') \<le> n
    else
      True"

text \<open>
  Also, we can compute the list of the longest blockchains in a given list of blockchains:
\<close>

abbreviation longest_chains :: "blockchain list \<Rightarrow> blockchain list" where
  "longest_chains \<CC> \<equiv>
    let
      is_longest_chain = \<lambda>\<C> \<CC>. \<forall>\<C>' \<in> set \<CC>. length \<C> \<ge> length \<C>'
    in
      [\<C>. \<C> \<leftarrow> \<CC>, is_longest_chain \<C> \<CC>]"

text \<open>
  Now we can define the function that implements the ``longest chain'' rule, namely the
  $\mathsf{maxvalid}$ function in the paper:
\<close>

abbreviation max_valid :: "blockchain \<Rightarrow> blockchain list \<Rightarrow> blockchain" where
  "max_valid \<C> \<CC> \<equiv>
    let
      \<CC>' = [\<C>'. \<C>' \<leftarrow> \<C> # \<CC>, forks_at_most k \<C> \<C>'];
      \<CC>'' = longest_chains \<CC>'
    in
      if \<C> \<in> set \<CC>'' then \<C> else hd \<CC>''"

subsubsection \<open> Blockchain extension \<close>

text \<open>
  In this section we model the procedure by which a stakeholder elected as a slot leader extends its
  current blockchain. We define a function that constructs a new block containing the transactions
  in the stakeholder's current state:
\<close>

abbreviation make_block :: "stakeholder_state \<Rightarrow> slot \<Rightarrow> vrf_value \<Rightarrow> block" where
  "make_block ss sl v \<equiv>
    let
      U\<^sub>i = ss_id ss;
      \<eta> = ss_\<eta> ss;
      st = if ss_\<C> ss = [] then None else Some (\<H> (last (ss_\<C> ss)));
      d = ss_txs ss;
      B\<^sub>\<pi> = (U\<^sub>i, v);
      \<rho> = evaluate_vrf (ss_sk\<^sub>v\<^sub>r\<^sub>f ss) (\<eta> \<bar>\<bar> sl \<bar>\<bar> NONCE);
      uB = (sl, st, d, B\<^sub>\<pi>, \<rho>);
      \<sigma> = sign (ss_sk\<^sub>k\<^sub>e\<^sub>s ss) uB
    in
      (uB, \<sigma>)"

text \<open>
  We can extend a stakeholder's current blockchain simply by appending a newly constructed block to
  it and updating its current state to the hash of this block:
\<close>

abbreviation extend_chain :: "stakeholder_state \<Rightarrow> block \<Rightarrow> stakeholder_state" where
  "extend_chain ss B\<^sub>n\<^sub>e\<^sub>w \<equiv> ss\<lparr>ss_\<C> := ss_\<C> ss @ [B\<^sub>n\<^sub>e\<^sub>w], ss_st := Some (\<H> B\<^sub>n\<^sub>e\<^sub>w)\<rparr>"

subsubsection \<open> Broadcast messages \<close>

text \<open>
  In addition to broadcasting transactions and blockchains, we also assume that there is a ``clock
  process'' broadcasting the next slot at the end of each current slot, see Section
  \ref{sec:semi-sync-model-ref}:
\<close>

datatype broadcast_msg =
    BroadcastTx (bm_tx: transaction)
  | BroadcastChain (bm_\<C>: blockchain)
  | BroadcastEndSlot (bm_sl: slot)

instance broadcast_msg :: countable
  by countable_datatype

type_synonym broadcast_channel = "broadcast_msg channel"

subsubsection \<open> The stakeholder process \<close>

text \<open>
  \label{sec:sh-process-ref}
  Now we are ready to define the process representing a stakeholder running the protocol:
\<close>

corec (friend) start_of_slot :: "
     broadcast_channel
  \<Rightarrow> stakeholder_state
  \<Rightarrow> slot
  \<Rightarrow> (broadcast_channel \<Rightarrow> stakeholder_state \<Rightarrow> slot \<Rightarrow> process)
  \<Rightarrow> process"
where
  "start_of_slot bc ss sl cont = (
    let
      T\<^sub>i = T(ss_id ss, slot_epoch sl, ss_G ss, ss_\<C> ss)
    in
      case is_slot_leader sl (ss_sk\<^sub>v\<^sub>r\<^sub>f ss) (ss_\<eta> ss) T\<^sub>i of
          None \<Rightarrow> \<zero> \<parallel> cont bc ss sl \<comment> \<open>\<open>\<zero> \<parallel>\<close> is added to fulfill corecursive function requirements\<close>
        | Some v \<Rightarrow>
          let
            B\<^sub>n\<^sub>e\<^sub>w = make_block ss sl v;
            ss' = extend_chain ss B\<^sub>n\<^sub>e\<^sub>w;
            ss'' = ss'\<lparr>ss_txs := []\<rparr>
          in
            bc \<triangleleft>\<degree> BroadcastChain (ss_\<C> ss'') \<parallel> cont bc ss'' sl)"

corec main_loop :: "broadcast_channel \<Rightarrow> stakeholder_state \<Rightarrow> slot \<Rightarrow> process" where
  "main_loop bc ss sl =
    bc \<triangleright>\<degree> msg. (
      case msg of
        BroadcastTx tx \<Rightarrow> (
          let
            ss' = ss\<lparr>ss_txs := tx # ss_txs ss\<rparr>
          in
            main_loop bc ss' sl)
      | BroadcastChain \<C> \<Rightarrow> (
          let
            \<C>\<^sub>p = prune_after sl \<C>; \<comment> \<open>pruned blocks belonging to future slots\<close>
            ss' = if verify_chain \<C>\<^sub>p (ss_G ss) (ss_\<eta> ss) then ss\<lparr>ss_\<CC> := \<C>\<^sub>p # ss_\<CC> ss\<rparr> else ss
          in
            main_loop bc ss' sl)
      | BroadcastEndSlot sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<Rightarrow> (
          let
            \<comment> \<open>If new epoch, compute epoch randomness\<close>
            ss' = if first_in_epoch sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t then ss\<lparr>ss_\<eta> := new_epoch_rnd\<rparr> else ss;
            \<comment> \<open>Update local chain\<close>
            \<C>\<^sub>m\<^sub>a\<^sub>x = max_valid (ss_\<C> ss') (ss_\<CC> ss');
            ss'' = ss'\<lparr>ss_\<C> := \<C>\<^sub>m\<^sub>a\<^sub>x, ss_st := Some (\<H> (last \<C>\<^sub>m\<^sub>a\<^sub>x)), ss_\<CC> := []\<rparr>
          in
            start_of_slot bc ss'' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t main_loop))"

abbreviation stakeholder :: "
     stakeholder_id
  \<Rightarrow> genesis
  \<Rightarrow> secret_key
  \<Rightarrow> secret_key
  \<Rightarrow> secret_key
  \<Rightarrow> broadcast_channel
  \<Rightarrow> process"
where
  "stakeholder U\<^sub>i G sk\<^sub>v\<^sub>r\<^sub>f sk\<^sub>k\<^sub>e\<^sub>s sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g bc \<equiv>
    let
      ss\<^sub>i\<^sub>n\<^sub>i\<^sub>t = init_stakeholder_state U\<^sub>i G sk\<^sub>v\<^sub>r\<^sub>f sk\<^sub>k\<^sub>e\<^sub>s sk\<^sub>d\<^sub>s\<^sub>i\<^sub>g
    in
      start_of_slot bc ss\<^sub>i\<^sub>n\<^sub>i\<^sub>t first_slot main_loop"

end
