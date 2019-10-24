(* TODO:

  - Factor out the common parts with `Relaying_Broadcasting_Equivalence.thy` and
    `Forwarding_Broadcasting_Equivalence.thy`.

*)
section \<open>
  Equivalence of a Diamond-Shaped Forwarding Network with Filtering-on-Receipt and its corresponding
  Filtering Broadcasting Network.
\<close>

theory Filtering_On_Receipt_Forwarding_Broadcasting_Equivalence
  imports
    Communication
begin

type_synonym four_node_network = "
  \<comment> \<open>Filtering predicate:\<close> (val \<Rightarrow> bool) \<Rightarrow>
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_send_interfacing = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Send buffer:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_send_buffering = "
  \<comment> \<open>Send buffer:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Links:\<close> [chan, chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_receive_interfacing = "
  \<comment> \<open>Filtering predicate:\<close> (val \<Rightarrow> bool) \<Rightarrow>
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Receive buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Send buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_receive_buffering = "
  \<comment> \<open>Receive buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Links:\<close> [chan, chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym diamond_core = "
  \<comment> \<open>Filtering predicate:\<close> (val \<Rightarrow> bool) \<Rightarrow>
  \<comment> \<open>Links:\<close> [chan, chan, chan, chan, chan] \<Rightarrow>
  process"

type_synonym cross_send_buffering = "
  \<comment> \<open>Send buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Broadcast medium:\<close> chan \<Rightarrow>
  process"

type_synonym cross_receive_buffering = "
  \<comment> \<open>Receive buffering:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Broadcast medium:\<close> chan \<Rightarrow>
  process"

type_synonym cross_send_interfacing = "
  \<comment> \<open>Send interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Broadcast medium:\<close> chan \<Rightarrow>
  process"

type_synonym cross_receive_interfacing = "
  \<comment> \<open>Filtering predicate:\<close> (val \<Rightarrow> bool) \<Rightarrow>
  \<comment> \<open>Receive interface:\<close> [chan, chan, chan, chan] \<Rightarrow>
  \<comment> \<open>Broadcast medium:\<close> chan \<Rightarrow>
  process"

abbreviation diamond_send_interfacing :: diamond_send_interfacing where
  "diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> ob\<^sub>3"

abbreviation diamond_send_buffering :: diamond_send_buffering where
  "diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Node 0:\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"

abbreviation diamond_receive_interfacing :: diamond_receive_interfacing where
  "diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    \<comment> \<open>Node 2:\<close> ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    \<comment> \<open>Node 3:\<close> ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3]"

abbreviation diamond_receive_buffering :: diamond_receive_buffering where
  "diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0"

abbreviation diamond :: four_node_network where
  "diamond \<phi> s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"

abbreviation receive_send_sidetrack where
  "receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<equiv>
    \<comment> \<open>Node 0:\<close> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3"

abbreviation relaying_core :: diamond_core where
  "relaying_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>From link 0--1:\<close> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>From link 0--2:\<close> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    \<comment> \<open>From link 1--3:\<close> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 2--3:\<close> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>From link 3--0:\<close> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>2"

abbreviation transformed_core :: diamond_core where
  "transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<equiv>
    \<comment> \<open>Link 0--1:\<close> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>1 \<parallel>
    \<comment> \<open>Link 0--2:\<close> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>2 \<parallel>
    \<comment> \<open>Link 1--3:\<close> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>1\<^sub>3 \<parallel>
    \<comment> \<open>Link 2--3:\<close> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>2\<^sub>3"

abbreviation cross_receive_buffering :: cross_receive_buffering where
  "cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> m \<rightarrow> ib\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> m \<rightarrow> ib\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> m \<rightarrow> ib\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> m \<rightarrow> ib\<^sub>3"

abbreviation cross_send_buffering :: cross_send_buffering where
  "cross_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> ob\<^sub>0 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<rightarrow> m"

abbreviation cross_receive_interfacing :: cross_receive_interfacing where
  "cross_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> m {\<phi>}\<rightarrow> r\<^sub>0 \<parallel>
    \<comment> \<open>Node 1:\<close> m {\<phi>}\<rightarrow> r\<^sub>1 \<parallel>
    \<comment> \<open>Node 2:\<close> m {\<phi>}\<rightarrow> r\<^sub>2 \<parallel>
    \<comment> \<open>Node 3:\<close> m {\<phi>}\<rightarrow> r\<^sub>3"

abbreviation cross_send_interfacing :: cross_send_interfacing where
  "cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<equiv>
    \<comment> \<open>Node 0:\<close> s\<^sub>0 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 1:\<close> s\<^sub>1 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 2:\<close> s\<^sub>2 \<rightarrow> m \<parallel>
    \<comment> \<open>Node 3:\<close> s\<^sub>3 \<rightarrow> m"

abbreviation cross where
  "cross \<phi> s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 \<equiv>
    \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      cross_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 m \<parallel>
      cross_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 m
    )"

lemma receive_send_sidetracking:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<comment> \<open>Node 0:\<close> (\<Prod>b\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?b \<parallel> ib\<^sub>0 {\<phi>}\<Rightarrow> [ob\<^sub>0, r\<^sub>0]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>b\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?b \<parallel> ib\<^sub>1 {\<phi>}\<Rightarrow> [ob\<^sub>1, r\<^sub>1]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>b\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?b \<parallel> ib\<^sub>2 {\<phi>}\<Rightarrow> [ob\<^sub>2, r\<^sub>2]) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Prod>b\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?b \<parallel> ib\<^sub>3 {\<phi>}\<Rightarrow> [ob\<^sub>3, r\<^sub>3])"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Node 0:\<close> (\<Prod>b\<leftarrow>[r\<^sub>0]. \<currency>\<^sup>?b \<parallel> ib\<^sub>0 {\<phi>}\<Rightarrow> [ob\<^sub>0, r\<^sub>0] \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>b\<leftarrow>[r\<^sub>1]. \<currency>\<^sup>?b \<parallel> ib\<^sub>1 {\<phi>}\<Rightarrow> [ob\<^sub>1, r\<^sub>1] \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>b\<leftarrow>[r\<^sub>2]. \<currency>\<^sup>?b \<parallel> ib\<^sub>2 {\<phi>}\<Rightarrow> [ob\<^sub>2, r\<^sub>2] \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (\<Prod>b\<leftarrow>[r\<^sub>3]. \<currency>\<^sup>?b \<parallel> ib\<^sub>3 {\<phi>}\<Rightarrow> [ob\<^sub>3, r\<^sub>3] \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3)"
    using sidetrack_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

(* TODO: Perhaps this is a coarse-grained step, overhaul it. *)
lemma core_relaying:
  shows "
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    relaying_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 {\<top>}\<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 {\<top>}\<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    \<comment> \<open>Node 1:\<close> (l\<^sub>0\<^sub>1 {\<top>}\<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1) \<parallel>
    \<comment> \<open>Node 2:\<close> (l\<^sub>0\<^sub>2 {\<top>}\<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2) \<parallel>
    \<comment> \<open>Node 3:\<close> (l\<^sub>1\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel>
                  (l\<^sub>2\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<Rightarrow> [l\<^sub>1\<^sub>3] \<parallel>
    ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<Rightarrow> [l\<^sub>2\<^sub>3] \<parallel>
    ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 {\<top>}\<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 {\<top>}\<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 {\<top>}\<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 {\<top>}\<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3]"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 {\<top>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 {\<top>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 {\<top>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 {\<top>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ob\<^sub>0 \<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel>
    l\<^sub>0\<^sub>1 \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel>
    l\<^sub>0\<^sub>2 \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel>
    l\<^sub>1\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3]"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 {\<top>}\<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 {\<top>}\<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 {\<top>}\<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 {\<top>}\<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2] \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    (l\<^sub>0\<^sub>1 {\<top>}\<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1) \<parallel>
    (l\<^sub>0\<^sub>2 {\<top>}\<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2) \<parallel>
    (l\<^sub>1\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel> (l\<^sub>2\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3) \<parallel>
    ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel>
    ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ob\<^sub>1 \<rightarrow> l\<^sub>1\<^sub>3 \<parallel>
    ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ob\<^sub>2 \<rightarrow> l\<^sub>2\<^sub>3 \<parallel>
    ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ob\<^sub>3 \<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy and distributor_shortcut_redundancy
    by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?b \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<Rightarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]) \<parallel>
    (l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0"
    unfolding duploss_def and unidirectional_bridge_def and general_parallel.simps
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    (\<currency>\<^sup>+l\<^sub>3\<^sub>0 \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> [l\<^sub>0\<^sub>1, l\<^sub>0\<^sub>2]. l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> b) \<parallel>
    (l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
    diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
    l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0"
    using distributor_split and unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding unidirectional_bridge_def and duploss_def and general_parallel.simps
    using natural_simps by equivalence
  finally show ?thesis .
qed

lemma core_transformation:
  shows "relaying_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat> transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
proof -
  have "relaying_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0)"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0) \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    (l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3 \<parallel> l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3 \<parallel> l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Left triangle:\<close>
    (l\<^sub>0\<^sub>1 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>1\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>1 \<parallel> l\<^sub>1\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Right triangle:\<close>
    (l\<^sub>0\<^sub>2 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>2\<^sub>3) \<parallel>
    l\<^sub>3\<^sub>0 {\<phi>}\<rightarrow> l\<^sub>0\<^sub>2 \<parallel> l\<^sub>2\<^sub>3 {\<phi>}\<rightarrow> l\<^sub>3\<^sub>0"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  finally show ?thesis .
qed

lemma receive_buffering_collapse:
  shows "
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>1 \<parallel> l\<^sub>0\<^sub>1 {\<top>}\<rightarrow> ib\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>2 \<parallel> l\<^sub>0\<^sub>2 {\<top>}\<rightarrow> ib\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>1\<^sub>3 \<parallel> l\<^sub>1\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>2\<^sub>3 \<parallel> l\<^sub>2\<^sub>3 {\<top>}\<rightarrow> ib\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<comment> \<open>Link 0--1:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> (l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 {\<top>}\<rightarrow> ib\<^sub>3) \<parallel>
    \<comment> \<open>Link 3--0:\<close> l\<^sub>3\<^sub>0 \<rightarrow> ib\<^sub>0"
    using unidirectional_bridge_source_switch by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat> ?q"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  finally show ?thesis .
qed

lemma send_buffering_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    cross_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0"
    (is "?p \<approx>\<^sub>\<flat> ?q")
proof -
  have "?p \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]. fst x {\<phi>}\<leftrightarrow>{\<phi>} snd x \<parallel>
                  ob\<^sub>0 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]. fst x {\<phi>}\<leftrightarrow>{\<phi>} snd x \<parallel> ob\<^sub>1 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]. fst x {\<phi>}\<leftrightarrow>{\<phi>} snd x \<parallel> ob\<^sub>2 \<Rightarrow> map snd [(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]. fst x {\<phi>}\<leftrightarrow>{\<phi>} snd x \<parallel>
                  ob\<^sub>0 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>1), (l\<^sub>3\<^sub>0, l\<^sub>0\<^sub>2)]) \<parallel>
    \<comment> \<open>Node 1:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]. fst x {\<phi>}\<leftrightarrow>{\<phi>} snd x \<parallel> ob\<^sub>1 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>1\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 2:\<close> (\<Prod>x\<leftarrow>[(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]. fst x {\<phi>}\<leftrightarrow>{\<phi>} snd x \<parallel> ob\<^sub>2 \<Rightarrow> map fst [(l\<^sub>3\<^sub>0, l\<^sub>2\<^sub>3)]) \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    by (intro
      basic_weak_parallel_preservation
      basic.weak.bisimilarity_reflexivity_rule
      distributor_target_switch [THEN basic.weak.bisimilarity_symmetry_rule]
    )
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0, l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<top> x ? l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> \<top> x ? l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<top> x ? l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> \<top> x ? l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    by simp
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<triangleright>\<^sup>\<infinity> x. (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> l\<^sub>3\<^sub>0 \<triangleleft> x)) \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using send_idempotency_under_duploss by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<triangleright>\<^sup>\<infinity> x. l\<^sub>3\<^sub>0 \<triangleleft> x) \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    using inner_duploss_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<flat>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> (\<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> ob\<^sub>0 \<triangleright>\<^sup>\<infinity> x. \<top> x ? l\<^sub>3\<^sub>0 \<triangleleft> x) \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    by simp
  also have "\<dots> \<approx>\<^sub>\<flat>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Node 0:\<close> ob\<^sub>0 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 1:\<close> ob\<^sub>1 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 2:\<close> ob\<^sub>2 \<Rightarrow> [l\<^sub>3\<^sub>0] \<parallel>
    \<comment> \<open>Node 3:\<close> ob\<^sub>3 \<Rightarrow> [l\<^sub>3\<^sub>0]"
    unfolding distributor_def and general_parallel.simps using natural_simps by equivalence
  finally show ?thesis .
qed

lemma core_collapse:
  shows "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<nu> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0"
proof -
  have "
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
      transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
    \<comment> \<open>Link 0--1:\<close> \<langle>0\<rangle> \<nu> l\<^sub>0\<^sub>1. (\<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>1) \<parallel>
    \<comment> \<open>Link 0--2:\<close> \<langle>1\<rangle> \<nu> l\<^sub>0\<^sub>2. (\<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>0\<^sub>2) \<parallel>
    \<comment> \<open>Link 1--3:\<close> \<langle>2\<rangle> \<nu> l\<^sub>1\<^sub>3. (\<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>1\<^sub>3) \<parallel>
    \<comment> \<open>Link 2--3:\<close> \<langle>3\<rangle> \<nu> l\<^sub>2\<^sub>3. (\<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> l\<^sub>3\<^sub>0 {\<phi>}\<leftrightarrow>{\<phi>} l\<^sub>2\<^sub>3)"
    using natural_simps by equivalence
  also have"\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    unfolding tagged_new_channel_def using duploss_detour_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>*l\<^sub>3\<^sub>0"
    using natural_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

lemma node_buffering_removal:
  shows "
    \<nu> ib ob. (\<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ib {\<phi>}\<rightarrow> ob)
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r"
proof -
  have "
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> m \<parallel> m \<rightarrow> ib \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ib {\<phi>}\<rightarrow> ob)
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ib {\<phi>}\<rightarrow> ob \<parallel> ob {\<top>}\<rightarrow> m \<parallel> m {\<top>}\<rightarrow> ib)"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ib {\<phi>}\<rightarrow> ob \<parallel> ob {\<top>}\<rightarrow> m \<parallel> m {\<top>}\<rightarrow> ib \<parallel> ob {\<top>}\<rightarrow> ib)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ob \<rightarrow> m \<parallel> ob \<rightarrow> ib \<parallel>
      m {\<top>}\<rightarrow> ib \<parallel> ib {\<phi>}\<rightarrow> ob)"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ob \<rightarrow> m \<parallel> ob \<rightarrow> ib \<parallel>
      m {\<top>}\<rightarrow> ib \<parallel> ib {\<phi>}\<rightarrow> ob \<parallel> m {\<phi>}\<rightarrow> ob)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> m \<rightarrow> ib \<parallel> m {\<phi>}\<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel>
      ib {\<phi>}\<rightarrow> ob \<parallel> ob {\<top>}\<rightarrow> m)"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> m \<rightarrow> ib \<parallel> m {\<phi>}\<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel>
      ib {\<phi>}\<rightarrow> ob \<parallel> ob {\<top>}\<rightarrow> m \<parallel> ib {\<phi>}\<rightarrow> m)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ob \<leftrightarrow>{\<phi>} m \<parallel> ib {\<phi>}\<leftrightarrow> ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>+m)"
    unfolding unidirectional_bridge_def and bidirectional_bridge_def and duploss_def
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ob \<leftrightarrow>{\<phi>} m \<parallel> ib {\<phi>}\<leftrightarrow> ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>+ib)"
    unfolding tagged_new_channel_def
    using
      duplication_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ib {\<phi>}\<leftrightarrow> ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>+ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>?m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<Rightarrow> [r, ob] \<parallel> ib {\<phi>}\<leftrightarrow> ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>+ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob)"
    unfolding tagged_new_channel_def
    using
      loss_channel_switch
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<leftrightarrow> ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel>
      \<currency>\<^sup>+ib \<parallel> \<Prod>b \<leftarrow> [r, ob]. \<currency>\<^sup>?b \<parallel> ib {\<phi>}\<Rightarrow> [r, ob])"
    unfolding general_parallel.simps using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ib {\<phi>}\<leftrightarrow> ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel>
      \<currency>\<^sup>+ib \<parallel> \<Prod>b \<leftarrow> [r, ob]. \<currency>\<^sup>?b \<parallel> \<Prod>b \<leftarrow> [r, ob]. ib {\<phi>}\<rightarrow> b)"
    using distributor_split by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> m \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib {\<phi>}\<rightarrow> r \<parallel>
      ib {\<phi>}\<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> ob \<parallel> ib {\<phi>}\<rightarrow> ob)"
    unfolding unidirectional_bridge_def and bidirectional_bridge_def and general_parallel.simps
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> ob \<rightarrow> ib \<parallel> m \<rightarrow> ib \<parallel> ob \<rightarrow> m \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib {\<phi>}\<rightarrow> r \<parallel>
      ib {\<phi>}\<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> ob)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib {\<phi>}\<rightarrow> r \<parallel> ib {\<phi>}\<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> ob \<parallel>
      ob {\<top>}\<rightarrow> m \<parallel> m {\<top>}\<rightarrow> ib \<parallel> ob {\<top>}\<rightarrow> ib)"
    unfolding unidirectional_bridge_def and bidirectional_bridge_def
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>?ob \<parallel> ib {\<phi>}\<rightarrow> r \<parallel> ib {\<phi>}\<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> ob \<parallel>
      ob {\<top>}\<rightarrow> m \<parallel> m {\<top>}\<rightarrow> ib)"
    using unidirectional_bridge_shortcut_redundancy by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> ib {\<phi>}\<rightarrow> r \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>*m)"
    unfolding bidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>+ib \<parallel> \<currency>\<^sup>?r \<parallel> ib {\<phi>}\<rightarrow> r \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>*ib)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> ib {\<phi>}\<rightarrow> r \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>*ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>*m)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (
      \<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> ib {\<phi>}\<rightarrow> r \<parallel> \<currency>\<^sup>?ob \<parallel> m \<leftrightarrow>{\<phi>} ib \<parallel> \<currency>\<^sup>*ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob)"
    unfolding tagged_new_channel_def
    using
      duploss_channel_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob \<parallel> ib {\<phi>}\<leftrightarrow> m \<parallel> ib {\<phi>}\<rightarrow> r)"
    unfolding duploss_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> s \<rightarrow> ob \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> m {\<phi>}\<leftrightarrow> ob \<parallel> \<currency>\<^sup>*ob \<parallel> ib {\<phi>}\<leftrightarrow> m \<parallel> m {\<phi>}\<rightarrow> r)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_source_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> \<currency>\<^sup>*ob \<parallel> ib {\<phi>}\<leftrightarrow> m \<parallel> m {\<phi>}\<rightarrow> r \<parallel> ob \<leftrightarrow>{\<phi>} m \<parallel> s {\<top>}\<rightarrow> ob)"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib. \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*m \<parallel> \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*ib \<parallel> \<currency>\<^sup>*ob \<parallel> ib {\<phi>}\<leftrightarrow> m \<parallel> m {\<phi>}\<rightarrow> r \<parallel> ob \<leftrightarrow>{\<phi>} m \<parallel> s {\<top>}\<rightarrow> m)"
    unfolding tagged_new_channel_def
    using
      unidirectional_bridge_target_switch and
      proper_weak_parallel_preservation_right and
      proper_weak_new_channel_preservation and
      basic_weak_bisimilarity_in_proper_weak_bisimilarity
    by (smt predicate2D)
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r \<parallel> \<langle>0\<rangle> \<nu> ib. (\<currency>\<^sup>*ib \<parallel> m \<leftrightarrow>{\<phi>} ib) \<parallel> \<langle>1\<rangle> \<nu> ob. (\<currency>\<^sup>*ob \<parallel> m {\<phi>}\<leftrightarrow> ob)"
    unfolding unidirectional_bridge_def using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r \<parallel> \<currency>\<^sup>*m \<parallel> \<currency>\<^sup>*m"
    unfolding tagged_new_channel_def using duploss_detour_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r \<parallel> \<currency>\<^sup>*m \<parallel> s \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r"
    using natural_simps by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

theorem diamond_cross_equivalence:
  shows "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    diamond \<phi> s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3
    \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    cross \<phi> s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
proof -
  have "
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )
    \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
        diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
      )
    )"
    using receive_send_sidetracking by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
        relaying_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using core_relaying by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      relaying_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
    )"
    using core_transformation by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      (
        transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using receive_buffering_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        diamond_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
        cross_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0
      )
    )"
    using send_buffering_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      (
        \<currency>\<^sup>*l\<^sub>3\<^sub>0 \<parallel>
        \<langle>8\<rangle> \<nu> l\<^sub>0\<^sub>1. \<langle>9\<rangle> \<nu> l\<^sub>0\<^sub>2. \<langle>10\<rangle> \<nu> l\<^sub>1\<^sub>3. \<langle>11\<rangle> \<nu> l\<^sub>2\<^sub>3. (
          \<currency>\<^sup>*l\<^sub>0\<^sub>1 \<parallel> \<currency>\<^sup>*l\<^sub>0\<^sub>2 \<parallel> \<currency>\<^sup>*l\<^sub>1\<^sub>3 \<parallel> \<currency>\<^sup>*l\<^sub>2\<^sub>3 \<parallel>
          transformed_core \<phi> l\<^sub>0\<^sub>1 l\<^sub>0\<^sub>2 l\<^sub>1\<^sub>3 l\<^sub>2\<^sub>3 l\<^sub>3\<^sub>0
        )
      )
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>4\<rangle> \<nu> ob\<^sub>0. \<langle>5\<rangle> \<nu> ob\<^sub>1. \<langle>6\<rangle> \<nu> ob\<^sub>2. \<langle>7\<rangle> \<nu> ob\<^sub>3.
    \<langle>12\<rangle> \<nu> l\<^sub>3\<^sub>0. (
      diamond_send_interfacing s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      diamond_receive_interfacing \<phi> r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3 ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      receive_send_sidetrack \<phi> ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 \<parallel>
      cross_receive_buffering ib\<^sub>0 ib\<^sub>1 ib\<^sub>2 ib\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      cross_send_buffering ob\<^sub>0 ob\<^sub>1 ob\<^sub>2 ob\<^sub>3 l\<^sub>3\<^sub>0 \<parallel>
      \<currency>\<^sup>*l\<^sub>3\<^sub>0
    )"
    unfolding tagged_new_channel_def using core_collapse by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>12\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      \<langle>0\<rangle> \<nu> ib\<^sub>0. \<langle>4\<rangle> \<nu> ob\<^sub>0. (
        \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> ob\<^sub>0 \<parallel> ob\<^sub>0 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>0 \<parallel> ib\<^sub>0 {\<phi>}\<Rightarrow> [r\<^sub>0, ob\<^sub>0] \<parallel> ib\<^sub>0 {\<phi>}\<rightarrow> ob\<^sub>0) \<parallel>
      \<langle>1\<rangle> \<nu> ib\<^sub>1. \<langle>5\<rangle> \<nu> ob\<^sub>1. (
        \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> ob\<^sub>1 \<parallel> ob\<^sub>1 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>1 \<parallel> ib\<^sub>1 {\<phi>}\<Rightarrow> [r\<^sub>1, ob\<^sub>1] \<parallel> ib\<^sub>1 {\<phi>}\<rightarrow> ob\<^sub>1) \<parallel>
      \<langle>2\<rangle> \<nu> ib\<^sub>2. \<langle>6\<rangle> \<nu> ob\<^sub>2. (
        \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> ob\<^sub>2 \<parallel> ob\<^sub>2 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>2 \<parallel> ib\<^sub>2 {\<phi>}\<Rightarrow> [r\<^sub>2, ob\<^sub>2] \<parallel> ib\<^sub>2 {\<phi>}\<rightarrow> ob\<^sub>2) \<parallel>
      \<langle>3\<rangle> \<nu> ib\<^sub>3. \<langle>7\<rangle> \<nu> ob\<^sub>3. (
        \<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> ob\<^sub>3 \<parallel> ob\<^sub>3 \<rightarrow> m \<parallel> m \<rightarrow> ib\<^sub>3 \<parallel> ib\<^sub>3 {\<phi>}\<Rightarrow> [r\<^sub>3, ob\<^sub>3] \<parallel> ib\<^sub>3 {\<phi>}\<rightarrow> ob\<^sub>3)
    )"
    using natural_simps by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp>
    \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel>
    \<langle>12\<rangle> \<nu> m. (
      \<currency>\<^sup>*m \<parallel>
      (\<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>0 \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r\<^sub>0) \<parallel>
      (\<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>1 \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r\<^sub>1) \<parallel>
      (\<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>2 \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r\<^sub>2) \<parallel>
      (\<currency>\<^sup>?r\<^sub>3 \<parallel> \<currency>\<^sup>*m \<parallel> s\<^sub>3 \<rightarrow> m \<parallel> m {\<phi>}\<rightarrow> r\<^sub>3)
    )"
    unfolding tagged_new_channel_def using node_buffering_removal by equivalence
  also have "\<dots> \<approx>\<^sub>\<sharp> \<currency>\<^sup>?r\<^sub>0 \<parallel> \<currency>\<^sup>?r\<^sub>1 \<parallel> \<currency>\<^sup>?r\<^sub>2 \<parallel> \<currency>\<^sup>?r\<^sub>3 \<parallel> cross \<phi> s\<^sub>0 s\<^sub>1 s\<^sub>2 s\<^sub>3 r\<^sub>0 r\<^sub>1 r\<^sub>2 r\<^sub>3"
    using natural_simps unfolding tagged_new_channel_def by equivalence
  finally show ?thesis unfolding tagged_new_channel_def .
qed

end
