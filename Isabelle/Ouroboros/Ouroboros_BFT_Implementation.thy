section \<open> Implementation of the Ouroboros BFT protocol \<close>

theory Ouroboros_BFT_Implementation
  imports Chi_Calculus.Typed_Basic_Transition_System "HOL-Library.BNF_Corec"
begin

subsection \<open> Cryptographic Primitives \<close>

subsubsection \<open> Hashing \<close>

text \<open>
  We will simply assume that we can compute the hash value of any value
\<close>

\<comment> \<open> Hash values \<close>
typedecl hash
axiomatization where hash_finite: "OFCLASS(hash, finite_class)"
instance hash :: finite by (rule hash_finite)

\<comment> \<open> A `perfect' hash function \<close>
consts hash :: "'a \<Rightarrow> hash"

text \<open>
  with no way of recovering @{typ 'a} from @{type hash}.
\<close>

subsubsection \<open> Public-Key infrastructure \<close>

text \<open>
  Public-key infrastructure depends on a pair of a public key and a private key:
\<close>

typedecl public_key

typedecl private_key

text \<open>
  We can sign a value using a private key:
\<close>

\<comment> \<open> Signatures \<close>
typedecl signature
axiomatization where signature_finite: "OFCLASS(signature, finite_class)"
instance signature :: finite by (rule signature_finite)

\<comment> \<open> Signing function \<close>
consts sign :: "private_key \<Rightarrow> 'a \<Rightarrow> signature"

text \<open>
  and verify signatures using a public key:
\<close>

\<comment> \<open> Signature verification function \<close>
consts verify :: "public_key \<Rightarrow> 'a \<Rightarrow> signature \<Rightarrow> bool"

subsection \<open> Environment Variables \<close>

text \<open>
  We bundle the environment variables used by the servers running the protocol in a record type:
\<close>

type_synonym u_param = nat

record server_env =
  se_u :: u_param \<comment> \<open> The `time-to-live' of a transaction in the mempool \<close>
  se_n :: nat \<comment> \<open> The number of servers running the protocol \<close>

subsection \<open> Data Types \<close>

subsubsection \<open> Slots \<close>

text \<open>
  We define the concept of slot:
\<close>

type_synonym slot = nat

text \<open>
  As defined in the paper, slot numbers begin at 1:
\<close>

abbreviation first_slot :: slot where
  "first_slot \<equiv> 1"

subsubsection \<open> Transactions \<close>

text \<open>
  We define the concept of transaction. As stated in the paper, this concept is an abstract one,
  therefore we model transactions as merely sequences of bits (following the tradition of
  Ouroboros papers):
\<close>
type_synonym transaction = string

subsubsection \<open> Genesis block \<close>

text \<open>
  As defined in the paper, we have a genesis block at the very start of a blockchain:
\<close>

record genesis =
  vks :: "public_key list" \<comment> \<open> list of servers' public keys \<close>

subsubsection \<open> Block \<close>

text \<open>
  We distinguish between an \<open>unsigned block\<close> (a block without a signature, a concept not explicitly
  present in the paper) and a signed block. Since the latter corresponds to the concept of a block
  in the paper, we refer to a signed block as simply a \<open>block\<close>:
\<close>

type_synonym unsigned_block = "
  hash option \<times> \<comment> \<open> Previous block hash. If first block then no previous block hash \<close>
  transaction list \<times> \<comment> \<open> Transaction data \<close>
  slot \<times> \<comment> \<open> Slot when the block was created \<close>
  signature" \<comment> \<open> Slot signature \<close>

type_synonym block = "unsigned_block \<times> signature"

subsubsection \<open> Blockchain \<close>

text \<open>
  A blockchain is simply a list of blocks:
\<close>

type_synonym blockchain = "block list"

text \<open>
  We do not record the genesis block explicitly and instead assume the genesis block is known to all
  servers.

  We define a function to prune the last \<open>k\<close> blocks in a blockchain:
\<close>

abbreviation prune_chain :: "blockchain \<Rightarrow> nat \<Rightarrow> blockchain" (infixl \<open>\<lceil>\<close> 999) where
  "\<C> \<lceil>k \<equiv> take (length \<C> - k) \<C>"

subsubsection \<open> Mempool \<close>

text \<open>
  Mempool entries consist of a transaction and the slot in which the transaction was created:
\<close>

type_synonym mempool = "(transaction \<times> slot) list"

subsection \<open> Leader Election \<close>

text \<open>
  Servers can compute the slot leader for any given slot number, being \<open>n\<close> the number of servers
  running the protocol:
\<close>

type_synonym server_index = nat \<comment> \<open> server indices begin at 1 \<close>

abbreviation slot_leader :: "slot \<Rightarrow> nat \<Rightarrow> server_index" where
  "slot_leader sl n \<equiv> (sl - 1) mod n + 1"

text \<open>
  Also, servers can ask if a given server is the slot leader for a given slot number:
\<close>

abbreviation is_slot_leader :: "slot \<Rightarrow> server_index \<Rightarrow> nat \<Rightarrow> bool" where
  "is_slot_leader sl i n \<equiv> i = slot_leader sl n"


subsection \<open> Verification \<close>

text \<open>
  A key component of verification is verifying that a transaction is consistent with a given current
  blockchain. However, the paper does not define what this notion of consistency means, so we leave
  this as an abstract concept:
\<close>

axiomatization
  is_consistent_tx_chain :: "transaction \<Rightarrow> blockchain \<Rightarrow> bool"
where
  empty_chain_tx_consistency: "is_consistent_tx_chain tx []"

text \<open>
  Based on this abstract definition, we can now verify that the transaction data in a block, i.e.
  the list of transactions in the block, is consistent with a given current blockchain:
\<close>

abbreviation is_consistent_tx_data_chain :: "transaction list \<Rightarrow> blockchain \<Rightarrow> bool" where
  "is_consistent_tx_data_chain d \<C> \<equiv> foldr (\<lambda>tx res. is_consistent_tx_chain tx \<C> \<and> res) d True"

text \<open>
  Another key component of verification is verifying that the signatures in a block are valid:
\<close>

fun verify_block_signatures :: "block \<Rightarrow> public_key \<Rightarrow> bool" where
  "verify_block_signatures ((h, d, sl, \<sigma>\<^sub>s\<^sub>l), \<sigma>\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k) vk =
    (verify vk sl \<sigma>\<^sub>s\<^sub>l \<and> verify vk (h, d, sl, \<sigma>\<^sub>s\<^sub>l) \<sigma>\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k)"

text \<open>
  In order to verify a block, we need some context: the hash of the previous block (if any),
  the public key of the block's slot leader, and the prefix of the current blockchain comprised by
  all the blocks preceding the block to be verified:
\<close>

abbreviation verify_block :: "block \<Rightarrow> hash option \<Rightarrow> public_key \<Rightarrow> blockchain \<Rightarrow> bool" where
  "verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v \<equiv> (
    let
      ((h, d, _, _), _) = B
    in (
      if \<not> verify_block_signatures B vk then
        False
      else (
        if \<not> is_consistent_tx_data_chain d \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v then
          False
        else (
          case oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v of
            None \<Rightarrow> True
          | Some h\<^sub>p\<^sub>r\<^sub>e\<^sub>v \<Rightarrow>
              the h = h\<^sub>p\<^sub>r\<^sub>e\<^sub>v)))) \<comment> \<open> if \<open>oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v\<close> is not \<open>None\<close> then \<open>h\<close> is not \<open>None\<close> either \<close>"

text \<open>
  Finally, we define a function to verify a blockchain:
\<close>

abbreviation verify_chain :: "blockchain \<Rightarrow> genesis \<Rightarrow> nat \<Rightarrow> bool" where
  "verify_chain \<C> G n \<equiv>
    fold (
      \<lambda>k res. res \<and> (
        let
          B = \<C> ! k; \<comment> \<open> current block \<close>
          ((_, _, sl, _), _) = B;
          oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v = (if k = 0 then None else fst (fst (\<C> ! (k - 1)))); \<comment> \<open> previous block hash \<close>
          i = slot_leader sl n; \<comment> \<open> index of slot leader for \<open>B\<close> \<close>
          vk\<^sub>i = vks G ! (i - 1); \<comment> \<open> public key of slot leader \<close>
          \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v = take k \<C> \<comment> \<open> sub-chain of \<open>\<C>\<close> previous to \<open>B\<close> \<close>
        in
          verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk\<^sub>i \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v))
      [0..<length \<C>]
      True"


subsection \<open> Protocol Implementation \<close>

subsubsection \<open> Server state \<close>

text \<open>
  Each server has access to its own state. We bundle the items comprising the server state in a
  record type:
\<close>

record server_state =
  ss_idx :: server_index \<comment> \<open> index of the server in the set of servers \<open>S\<^sub>1, ..., S\<^sub>n\<close> \<close>
  ss_G :: genesis \<comment> \<open> genesis block \<close>
  ss_\<C> :: blockchain \<comment> \<open> current blockchain \<close>
  ss_mempool :: mempool \<comment> \<open> current mempool \<close>
  ss_sk :: private_key \<comment> \<open> private key \<close>

text \<open>
  We can specify what the initial state for each server should be:
\<close>

abbreviation init_server_state :: "server_index \<Rightarrow> genesis \<Rightarrow> private_key \<Rightarrow> server_state" where
  "init_server_state i G sk \<equiv> \<lparr>ss_idx = i, ss_G = G, ss_\<C> = [], ss_mempool = [], ss_sk = sk\<rparr>"

subsubsection \<open> Mempool update \<close>

text \<open>
  A key component of mempool update is verifying that a transaction is consistent with a given
  current mempool. However, the paper does not define what this notion of consistency means, so we
  leave this as an abstract concept:
\<close>

axiomatization
  is_consistent_tx_mempool :: "transaction \<Rightarrow> mempool \<Rightarrow> bool"
where
  empty_mempool_tx_consistency: "is_consistent_tx_mempool tx []"

text \<open>
  Now, a transaction is consistent with a server state whenever is consistent with both the server
  state's mempool and blockchain:
\<close>

abbreviation is_consistent_tx :: "transaction \<Rightarrow> server_state \<Rightarrow> bool" where
  "is_consistent_tx tx ss \<equiv>
    is_consistent_tx_mempool tx (ss_mempool ss) \<and> is_consistent_tx_chain tx (ss_\<C> ss)"

text \<open>
  Finally, we can add a transaction to the server's mempool as long as it is consistent with the
  server state:
\<close>

abbreviation update_mempool :: "server_state \<Rightarrow> transaction \<Rightarrow> slot \<Rightarrow> server_state" where
  "update_mempool ss tx sl \<equiv> (
    if is_consistent_tx tx ss then
      ss\<lparr>ss_mempool := (tx, sl) # ss_mempool ss\<rparr>
    else
      ss)"

subsubsection \<open> Blockchain update \<close>

text \<open>
  We can replace the server's current blockchain with a new one provided it is longer and valid:
\<close>

fun update_chain :: "server_state \<Rightarrow> nat \<Rightarrow> blockchain \<Rightarrow> server_state" where
  "update_chain ss n \<C> = (
    if length \<C> > length (ss_\<C> ss) \<and> verify_chain \<C> (ss_G ss) n then
      ss\<lparr>ss_\<C> := \<C>\<rparr>
    else
      ss)"

subsubsection \<open> Blockchain extension \<close>

text \<open>
  We need a function that removes the `old' transactions from the server's mempool, i.e. the
  transactions that have been maintained for \<open>u\<close> rounds:
\<close>

abbreviation prune_mempool :: "server_state \<Rightarrow> slot \<Rightarrow> u_param \<Rightarrow> server_state" where
  "prune_mempool ss sl u \<equiv> ss\<lparr>ss_mempool := filter (\<lambda>(_, sl'). sl - sl' + 1 < u) (ss_mempool ss)\<rparr>"

text \<open>
  We define a function that builds a new block containing the transactions in the server's
  current mempool. A pre-condition for using this function is that @{const prune_mempool} must be
  called beforehand so that the mempool already contains only the valid transactions:
\<close>
abbreviation make_block :: "server_state \<Rightarrow> slot \<Rightarrow> block" where
  "make_block ss sl \<equiv> (
    let
      h = (if ss_\<C> ss = [] then None else Some (hash (last (ss_\<C> ss))));
      d = map fst (ss_mempool ss);
      \<sigma>sl = sign (ss_sk ss) sl;
      uB = (h, d, sl, \<sigma>sl)
    in
      (uB, sign (ss_sk ss) uB))"

text \<open>
  We can extend a server's current blockchain simply by appending a newly constructed block to it:
\<close>

abbreviation extend_chain where
  "extend_chain ss B\<^sub>n\<^sub>e\<^sub>w \<equiv> ss\<lparr>ss_\<C> := ss_\<C> ss @ [B\<^sub>n\<^sub>e\<^sub>w]\<rparr>"

text \<open>
  Finally, we need a function to empty the server's mempool in preparation for the next round:
\<close>

abbreviation clear_mempool :: "server_state \<Rightarrow> server_state" where
  "clear_mempool ss \<equiv> ss\<lparr>ss_mempool := []\<rparr>"

subsubsection \<open> Broadcast messages \<close>

text \<open>
  In addition to broadcasting transactions and blockchains, we also assume that there is a `clock
  process' broadcasting the next slot at the end of each current slot:
\<close>

datatype broadcast_msg =
    BroadcastTx (bm_tx: transaction)
  | BroadcastChain (bm_\<C>: blockchain)
  | BroadcastEndSlot (bm_sl: slot)

instance broadcast_msg :: countable
  by countable_datatype

type_synonym receive_channel = "broadcast_msg channel"

type_synonym send_channel = "broadcast_msg channel"

subsubsection \<open> The server process \<close>

text \<open>
  Now we are ready to define the process representing a server running the protocol:
\<close>

corec main_loop :: "send_channel \<Rightarrow> receive_channel \<Rightarrow> server_env \<Rightarrow> server_state \<Rightarrow> slot \<Rightarrow> process"
where
  "main_loop s r \<Gamma> ss sl =
    r \<triangleright>\<degree> msg. (
      case msg of
        BroadcastTx tx \<Rightarrow> (
          let
            ss' = update_mempool ss tx sl
          in
            main_loop s r \<Gamma> ss' sl)
      | BroadcastChain \<C> \<Rightarrow> (
          let
            ss' = update_chain ss (se_n \<Gamma>) \<C>
          in
            main_loop s r \<Gamma> ss' sl)
      | BroadcastEndSlot sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t \<Rightarrow> (
          let
            ss' = prune_mempool ss sl (se_u \<Gamma>)
          in (
            if is_slot_leader sl (ss_idx ss) (se_n \<Gamma>) then (
              let
                B\<^sub>n\<^sub>e\<^sub>w = make_block ss' sl;
                ss'' = extend_chain ss' B\<^sub>n\<^sub>e\<^sub>w;
                ss''' = clear_mempool ss''
              in
                s \<triangleleft>\<degree> BroadcastChain (ss_\<C> ss''') \<parallel> main_loop s r \<Gamma> ss''' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t)
            else
              main_loop s r \<Gamma> ss' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t)))"

abbreviation server ::
  "send_channel \<Rightarrow> receive_channel \<Rightarrow> genesis \<Rightarrow> server_env \<Rightarrow> server_index \<Rightarrow> private_key \<Rightarrow> process"
where
  "server s r G \<Gamma> i sk \<equiv> (
    let
      ss\<^sub>i\<^sub>n\<^sub>i\<^sub>t = init_server_state i G sk
    in
      main_loop s r \<Gamma> ss\<^sub>i\<^sub>n\<^sub>i\<^sub>t first_slot)"

subsection \<open> Proofs \<close>

text \<open>
  This section contains lemmas for proving the correctness of the functions defined in previous
  sections, some of them according to specific scenarios, i.e. using specific data sets.
\<close>

subsubsection \<open> Proofs for @{const is_consistent_tx_data_chain}\<close>

lemma empty_chain_tx_data_consistency: "is_consistent_tx_data_chain d []"
  by (induction d) (auto simp add: empty_chain_tx_consistency)

lemma tx_data_chain_consistency:
  assumes "\<forall>i \<in> {0..<length d}. is_consistent_tx_chain (d ! i) \<C>"
  shows "is_consistent_tx_data_chain d \<C>"
  using assms
  by (induction d) (auto dest: bspec, force)

lemma tx_data_chain_inconsistency:
  assumes "\<exists>i \<in> {0..<length d}. \<not> is_consistent_tx_chain (d ! i) \<C>"
  shows "\<not> is_consistent_tx_data_chain d \<C>"
  using assms by (induction d) (simp, force simp add: less_Suc_eq_0_disj)

subsubsection \<open> Proofs for @{const update_mempool}\<close>

lemma update_mempool_consistency:
  assumes "is_consistent_tx tx ss"
  shows "update_mempool ss tx sl = ss\<lparr>ss_mempool := (tx, sl) # ss_mempool ss\<rparr>"
  using assms by simp

lemma update_mempool_inconsistency:
  assumes "\<not> is_consistent_tx tx ss"
  shows "update_mempool ss tx sl = ss"
  using assms by simp

subsubsection \<open> Proofs for @{const verify_block}\<close>

lemma signatures_block_invalidity:
  assumes "\<not> verify_block_signatures B vk"
  shows "\<not> verify_block B oB\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  using assms by auto

lemma tx_data_chain_block_invalidity:
  assumes "\<not> is_consistent_tx_data_chain d \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  shows "\<not> verify_block ((h, d, sl, \<sigma>\<^sub>s\<^sub>l), \<sigma>\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k) oB\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  using assms by simp

lemma first_block_validity:
  assumes "B = ((h, d, sl, \<sigma>\<^sub>s\<^sub>l), \<sigma>\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k)"
  and "verify_block_signatures B vk"
  and "is_consistent_tx_data_chain d \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  and "oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v = None"
  shows "verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  using assms by simp

lemma intermediate_block_validity:
  assumes "B = ((h, d, sl, \<sigma>\<^sub>s\<^sub>l), \<sigma>\<^sub>b\<^sub>l\<^sub>o\<^sub>c\<^sub>k)"
  and "verify_block_signatures B vk"
  and "is_consistent_tx_data_chain d \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  and "oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v = Some h\<^sub>p\<^sub>r\<^sub>e\<^sub>v"
  shows "verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v = (the h = h\<^sub>p\<^sub>r\<^sub>e\<^sub>v)"
  using assms by simp

subsubsection \<open> Proofs for @{const slot_leader}\<close>

lemma two_server_network_odd_slot_leadership:
  assumes "n = 2"
  and "odd sl"
  shows "slot_leader sl n = 1"
  using assms by simp

lemma two_server_network_even_slot_leadership:
  assumes "n = 2"
  and "sl > 0" \<comment> \<open> slots begin at 1, so \<open>sl > 0\<close> always holds \<close>
  and "even sl"
  shows "slot_leader sl n = 2"
  using assms by (simp add: mod2_eq_if)

subsubsection \<open> Proofs for @{const verify_chain}\<close>

lemma block_signatures_chain_validity:
  assumes "G = \<lparr>vks = [vk\<^sub>1, vk\<^sub>2]\<rparr>"
  and "n = 2"
  and "sl\<^sub>1 = 1"
  and "B\<^sub>1 = ((None, [tx\<^sub>1], sl\<^sub>1, \<sigma>sl\<^sub>1), \<sigma>B\<^sub>1)"
  and "\<C> = [B\<^sub>1]"
  and "verify_block_signatures B\<^sub>1 vk\<^sub>1"
  shows "verify_chain \<C> G n"
proof -
  from assms(1,3-5) have "verify_chain \<C> G n = verify_block B\<^sub>1 None vk\<^sub>1 []"
    by simp
  moreover from assms(6) have "verify_block B\<^sub>1 None vk\<^sub>1 []"
    by (auto simp add: empty_chain_tx_data_consistency)
  ultimately show ?thesis
    by simp
qed

lemma block_signatures_chain_invalidity:
  assumes "G = \<lparr>vks = [vk\<^sub>1, vk\<^sub>2]\<rparr>"
  and "n = 2"
  and "sl\<^sub>1 = 1"
  and "B\<^sub>1 = ((None, [tx\<^sub>1], sl\<^sub>1, \<sigma>sl\<^sub>1), \<sigma>B\<^sub>1)"
  and "\<C> = [B\<^sub>1]"
  and "\<not> verify_block_signatures B\<^sub>1 vk\<^sub>1"
  shows "\<not> verify_chain \<C> G n"
proof -
  from assms(1,3-5) have "verify_chain \<C> G n = verify_block B\<^sub>1 None vk\<^sub>1 []"
    by simp
  moreover from assms(6) have "\<not> verify_block B\<^sub>1 None vk\<^sub>1 []"
    using empty_chain_tx_data_consistency by auto
  ultimately show ?thesis
    by simp
qed

lemma verify_chain_split:
  assumes "G = \<lparr>vks = [vk\<^sub>1, vk\<^sub>2]\<rparr>"
  and "n = 2"
  and "sl\<^sub>1 = 1"
  and "uB\<^sub>1 = (None, [tx\<^sub>1], sl\<^sub>1, \<sigma>sl\<^sub>1)"
  and "B\<^sub>1 = (uB\<^sub>1, \<sigma>B\<^sub>1)"
  and "sl\<^sub>2 = 2"
  and "oh\<^sub>1 = Some (hash uB\<^sub>1)"
  and "B\<^sub>2 = ((oh\<^sub>1, [tx\<^sub>2, tx\<^sub>3], sl\<^sub>2, \<sigma>sl\<^sub>2), \<sigma>B\<^sub>2)"
  and "\<C> = [B\<^sub>1, B\<^sub>2]"
  shows "verify_chain \<C> G n = (verify_block B\<^sub>1 None vk\<^sub>1 [] \<and> verify_block B\<^sub>2 oh\<^sub>1 vk\<^sub>2 [B\<^sub>1])"
proof -
  let ?f = "
    \<lambda>k res. res \<and> (
      let
        B = \<C> ! k;
        ((_, _, sl, _), _) = B;
        oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v = (if k = 0 then None else fst (fst (\<C> ! (k - 1))));
        i = slot_leader sl n;
        vk\<^sub>i = vks G ! (i - 1);
        \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v = take k \<C>
      in
        verify_block B oh\<^sub>p\<^sub>r\<^sub>e\<^sub>v vk\<^sub>i \<C>\<^sub>p\<^sub>r\<^sub>e\<^sub>v)"
  from assms(9) have "verify_chain \<C> G n = fold ?f [0, 1] True"
    by simp
  also have "\<dots> = ?f 1 (?f 0 True)"
    unfolding Let_def and One_nat_def by simp
  also from assms(1-5,9) have "\<dots> = ?f 1 (verify_block B\<^sub>1 None vk\<^sub>1 [])"
    by simp
  also from assms(1,2,4-9) have "\<dots> = (verify_block B\<^sub>1 None vk\<^sub>1 [] \<and> verify_block B\<^sub>2 oh\<^sub>1 vk\<^sub>2 [B\<^sub>1])"
    by simp
  finally show ?thesis .
qed

lemma non_singleton_chain_validity:
  assumes "G = \<lparr>vks = [vk\<^sub>1, vk\<^sub>2]\<rparr>"
  and "n = 2"
  and "sl\<^sub>1 = 1"
  and "uB\<^sub>1 = (None, [tx\<^sub>1], sl\<^sub>1, \<sigma>sl\<^sub>1)"
  and "B\<^sub>1 = (uB\<^sub>1, \<sigma>B\<^sub>1)"
  and "sl\<^sub>2 = 2"
  and "oh\<^sub>1 = Some (hash uB\<^sub>1)"
  and "B\<^sub>2 = ((oh\<^sub>1, [tx\<^sub>2, tx\<^sub>3], sl\<^sub>2, \<sigma>sl\<^sub>2), \<sigma>B\<^sub>2)"
  and "\<C> = [B\<^sub>1, B\<^sub>2]"
  and "verify_block_signatures B\<^sub>1 vk\<^sub>1"
  and "verify_block_signatures B\<^sub>2 vk\<^sub>2"
  and "is_consistent_tx_data_chain [tx\<^sub>2, tx\<^sub>3] [B\<^sub>1]"
  shows "verify_chain \<C> G n"
proof -
  from assms(10) have "verify_block B\<^sub>1 None vk\<^sub>1 []"
    using empty_chain_tx_data_consistency by (simp add: case_prod_beta')
  moreover from assms(2,4,6,7,8,11,12) have "verify_block B\<^sub>2 oh\<^sub>1 vk\<^sub>2 [B\<^sub>1]"
    by simp
  ultimately have "verify_block B\<^sub>1 None vk\<^sub>1 [] \<and> verify_block B\<^sub>2 oh\<^sub>1 vk\<^sub>2 [B\<^sub>1]"
    by simp
  moreover from assms(1-9) have "
    (verify_block B\<^sub>1 None vk\<^sub>1 [] \<and> verify_block B\<^sub>2 oh\<^sub>1 vk\<^sub>2 [B\<^sub>1]) = verify_chain \<C> G n"
    by (simp add: verify_chain_split)
  ultimately show ?thesis
    by simp
qed

subsubsection \<open> Proofs for @{const update_chain}\<close>

lemma not_longer_chain_update:
  assumes "length \<C> \<le> length (ss_\<C> ss)"
  shows "update_chain ss n \<C> = ss"
  using assms by simp

lemma invalid_chain_update:
  assumes "\<not> verify_chain \<C> (ss_G ss) n"
  shows "update_chain ss n \<C> = ss"
  using assms by simp

lemma longer_and_valid_chain_update:
  assumes "length \<C> > length (ss_\<C> ss)"
  and "verify_chain \<C> (ss_G ss) n"
  shows "update_chain ss n \<C> = ss\<lparr>ss_\<C> := \<C>\<rparr>"
  using assms by simp

subsubsection \<open> Proofs for @{const prune_mempool}\<close>

text \<open>
  The lemma in this section uses the following timeline of arrival of transactions:

  \begin{tabular}{|c|c|c|c|}
  \hline
  slot & $tx_1$   & $tx_2$   & $tx_3$   \\ \hline
  1    & $\times$ &          &          \\ \hline
  2    & $\times$ &          &          \\ \hline
  3    & $\times$ & $\times$ &          \\ \hline
  4    & $\times$ & $\times$ & $\times$ \\ \hline
  \end{tabular}
\<close>

lemma mempool_prunning:
  assumes "ss_mempool ss = [(tx\<^sub>1, 1), (tx\<^sub>2, 3), (tx\<^sub>3, 4)]"
  and "sl = 4"
  and "u = 4"
  shows "ss_mempool (prune_mempool ss sl u) = [(tx\<^sub>2, 3), (tx\<^sub>3, 4)]"
  using assms by simp

subsubsection \<open> Proofs for @{const make_block}\<close>

lemma first_block_creation:
  assumes "ss_mempool ss = [(tx\<^sub>2, 3), (tx\<^sub>3, 4)]"
  and "sl = 4"
  and "ss_\<C> ss = []"
  and "uB\<^sub>1 = (None, [tx\<^sub>2, tx\<^sub>3], sl, sign (ss_sk ss) sl)"
  and "B\<^sub>1 = (uB\<^sub>1, sign (ss_sk ss) uB\<^sub>1)"
  shows "make_block ss sl = B\<^sub>1"
  using assms by (simp, metis)

lemma second_block_creation:
  assumes "ss_mempool ss = [(tx\<^sub>2, 3), (tx\<^sub>3, 4)]"
  and "sl = 10"
  and "B\<^sub>1 = ((None, [tx\<^sub>0], sl\<^sub>1, \<sigma>sl\<^sub>1), \<sigma>B\<^sub>1)"
  and "ss_\<C> ss = [B\<^sub>1]"
  and "uB\<^sub>2 = (Some (hash B\<^sub>1), [tx\<^sub>2, tx\<^sub>3], sl, sign (ss_sk ss) sl)"
  and "B\<^sub>2 = (uB\<^sub>2, sign (ss_sk ss) uB\<^sub>2)"
  shows "make_block ss sl = B\<^sub>2"
  using assms by (simp, metis)

subsubsection \<open> Proofs for @{const main_loop}\<close>

lemma main_loop_end_slot_no_mining:
  assumes "msg = BroadcastEndSlot sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t"
  and "\<Gamma> = \<lparr>se_u = 4, se_n = 2\<rparr>"
  and "ss = \<lparr>
    ss_idx = 1,
    ss_G = \<lparr>vks = [vk\<^sub>1, vk\<^sub>2]\<rparr>,
    ss_\<C> = [B\<^sub>1],
    ss_mempool = [(tx\<^sub>1, 1), (tx\<^sub>2, 3), (tx\<^sub>3, 4)],
    ss_sk = sk\<^sub>1\<rparr>"
  and "sl = 4"
  and "ss' = ss\<lparr>ss_mempool := [(tx\<^sub>2, 3), (tx\<^sub>3, 4)]\<rparr>"
  shows "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> ss' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t"
proof -
  from assms(1) have "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> (
    let
      ss'' = prune_mempool ss sl (se_u \<Gamma>)
    in (
      if is_slot_leader sl (ss_idx ss) (se_n \<Gamma>) then (
        let
          B\<^sub>n\<^sub>e\<^sub>w = make_block ss'' sl;
          ss''' = extend_chain ss'' B\<^sub>n\<^sub>e\<^sub>w;
          ss'''' = clear_mempool ss'''
        in
          s \<triangleleft>\<degree> BroadcastChain (ss_\<C> ss'''') \<parallel> main_loop s r \<Gamma> ss'''' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t)
      else
        main_loop s r \<Gamma> ss'' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t))"
    using broadcast_msg.simps(12) and main_loop.code and receiving and typed_untyped_value
    by (metis (no_types, lifting))
  with assms(2-5) show ?thesis
    by auto
qed

lemma main_loop_end_slot_mining:
  assumes "msg = BroadcastEndSlot sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t"
  and "\<Gamma> = \<lparr>se_u = 4, se_n = 2\<rparr>"
  and "B\<^sub>1 = ((None, [tx\<^sub>0], sl\<^sub>1, \<sigma>sl\<^sub>1), \<sigma>B\<^sub>1)"
  and "ss = \<lparr>
    ss_idx = 2,
    ss_G = \<lparr>vks = [vk\<^sub>1, vk\<^sub>2]\<rparr>,
    ss_\<C> = [B\<^sub>1],
    ss_mempool = [(tx\<^sub>1, 1), (tx\<^sub>2, 3), (tx\<^sub>3, 4)],
    ss_sk = sk\<^sub>1\<rparr>"
  and "sl = 4"
  and "uB\<^sub>2 = (Some (hash B\<^sub>1), [tx\<^sub>2, tx\<^sub>3], sl, sign (ss_sk ss) sl)"
  and "B\<^sub>2 = (uB\<^sub>2, sign (ss_sk ss) uB\<^sub>2)"
  and "\<C>\<^sub>n\<^sub>e\<^sub>w = [B\<^sub>1, B\<^sub>2]"
  and "ss' = ss\<lparr>ss_\<C> := \<C>\<^sub>n\<^sub>e\<^sub>w, ss_mempool := []\<rparr>"
  shows "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> s \<triangleleft>\<degree> BroadcastChain \<C>\<^sub>n\<^sub>e\<^sub>w \<parallel> main_loop s r \<Gamma> ss' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t"
proof -
  let ?ss'' = "ss\<lparr>ss_mempool := [(tx\<^sub>2, 3), (tx\<^sub>3, 4)]\<rparr>"
  let ?ss''' = "?ss''\<lparr>ss_\<C> := \<C>\<^sub>n\<^sub>e\<^sub>w\<rparr>"
  from assms(2,4,5) have "is_slot_leader sl (ss_idx ss) (se_n \<Gamma>)"
    by simp
  moreover have f1: "prune_mempool ss sl (se_u \<Gamma>) = ?ss''"
    using assms(2,4,5) and mempool_prunning by simp
  with assms(4,6,7) have f2: "make_block ?ss'' sl = B\<^sub>2"
    by (auto, metis)
  with assms(4,8) have f3: "extend_chain ?ss'' B\<^sub>2 = ?ss'''"
    by simp
  with assms(4,9) have f4: "clear_mempool ?ss''' = ss'"
    by simp
  moreover from assms(1) have "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> (
    let
      ss'' = prune_mempool ss sl (se_u \<Gamma>)
    in (
      if is_slot_leader sl (ss_idx ss) (se_n \<Gamma>) then (
        let
          B\<^sub>n\<^sub>e\<^sub>w = make_block ss'' sl;
          ss''' = extend_chain ss'' B\<^sub>n\<^sub>e\<^sub>w;
          ss'''' = clear_mempool ss'''
        in
          s \<triangleleft>\<degree> BroadcastChain (ss_\<C> ss'''') \<parallel> main_loop s r \<Gamma> ss'''' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t)
      else
        main_loop s r \<Gamma> ss'' sl\<^sub>n\<^sub>e\<^sub>x\<^sub>t))"
    using broadcast_msg.simps(12) and main_loop.code and receiving and typed_untyped_value
    by (metis (no_types, lifting))
  ultimately show ?thesis
    using f1 and f2 and f3 and f4 and assms(4)
    by (smt server_state.select_convs(2,3) server_state.update_convs(2-4))
qed

lemma main_loop_consistent_tx_reception:
  assumes "msg = BroadcastTx tx"
  and "is_consistent_tx tx ss"
  and "ss' = ss\<lparr>ss_mempool := (tx, sl) # ss_mempool ss\<rparr>"
  shows "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> ss' sl"
proof -
  from assms(1) have "
    main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> (update_mempool ss tx sl) sl"
    using broadcast_msg.simps(10) and main_loop.code and receiving and typed_untyped_value
    by (metis (no_types, lifting))
  with assms(2,3) show ?thesis
    by simp
qed

lemma main_loop_inconsistent_tx_reception:
  assumes "msg = BroadcastTx tx"
  and "\<not> is_consistent_tx tx ss"
  shows "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> ss sl"
proof -
  from assms(1) have "
    main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> (update_mempool ss tx sl) sl"
    using broadcast_msg.simps(10) and main_loop.code and receiving and typed_untyped_value
    by (metis (no_types, lifting))
  moreover from assms(2) have "update_mempool ss tx sl = ss"
    by simp
  ultimately show ?thesis
    by simp
qed

lemma main_loop_not_longer_chain_reception:
  assumes "length \<C> \<le> length (ss_\<C> ss)"
  and "msg = BroadcastChain \<C>"
  shows "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> ss sl"
proof -
  from assms(2) have "
    main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> (update_chain ss (se_n \<Gamma>) \<C>) sl"
    using broadcast_msg.simps(11) and main_loop.code and receiving and typed_untyped_value
    by (metis (no_types, lifting))
  moreover from assms(1) have "update_chain ss (se_n \<Gamma>) \<C> = ss"
    using not_longer_chain_update by simp
  ultimately show ?thesis
    by simp
qed

lemma main_loop_longer_and_valid_chain_reception:
  assumes "length \<C> > length (ss_\<C> ss)"
  and "verify_chain \<C> (ss_G ss) (se_n \<Gamma>)"
  and "msg = BroadcastChain \<C>"
  and "ss' = ss\<lparr>ss_\<C> := \<C>\<rparr>"
  shows "main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> ss' sl"
proof -
  from assms(3) have "
    main_loop s r \<Gamma> ss sl \<rightarrow>\<^sub>\<flat>\<lbrace>r \<triangleright>\<degree> msg\<rbrace> main_loop s r \<Gamma> (update_chain ss (se_n \<Gamma>) \<C>) sl"
    using broadcast_msg.simps(11) and main_loop.code and receiving and typed_untyped_value
    by (metis (no_types, lifting))
  moreover from assms(1,2) have "update_chain ss (se_n \<Gamma>) \<C> = ss\<lparr>ss_\<C> := \<C>\<rparr>"
    using longer_and_valid_chain_update by simp
  ultimately show ?thesis
    using assms(4) by simp
qed

end
