section \<open> Proof of the chain selection property \<close>

theory Chain_Selection_Property
  imports Main
begin

subsection \<open> Introduction \<close>

text \<open>
  In this work we formally verify an implementation of the Ouroboros chain selection rule. It is
  important to note that this work does not take into account the condition that a candidate chain
  must not fork more than \<open>k\<close> blocks from the current local chain. The reason for this omission is
  that, should we include that extra condition, the verification would not be possible. To see this,
  consider the following counterexample: Assume that \<open>k = 2\<close>, the local chain \<open>\<C>\<close> is \<open>\<G>-A-B-C\<close>, and
  the candidate chains \<open>\<C>\<^sub>1\<close> and \<open>\<C>\<^sub>2\<close> are \<open>\<G>-A-B-D-E-F\<close> and \<open>\<G>-A-B-G-H-I-J\<close>, respectively, and
  received in that order. Let $\mathsf{maxvalid}_p$ denote the pairwise comparison version of the
  usual $\mathsf{maxvalid}$ function as defined in the Ouroboros paper. Thus, we have that
  $\mathsf{maxvalid}$\<open>(\<C>, [\<C>\<^sub>1, \<C>\<^sub>2]) = \<C>\<^sub>2\<close> (since \<open>\<C>\<^sub>1\<close> and \<open>\<C>\<^sub>2\<close> are valid forks of \<open>\<C>\<close> and \<open>\<C>\<^sub>2\<close> is the
  longest one), but $\mathsf{maxvalid}_p$\<open>(\<C>, \<C>\<^sub>1) = \<C>\<^sub>1\<close> (since \<open>\<C>\<^sub>1\<close> is a valid fork of \<open>\<C>\<close> plus it is
  longer) and $\mathsf{maxvalid}_p$\<open>(\<C>\<^sub>1, \<C>\<^sub>2) = \<C>\<^sub>1\<close> (since \<open>\<C>\<^sub>2\<close> forks from \<open>\<C>\<^sub>1\<close> by 3 blocks).
\<close>

subsection \<open> Preliminaries \<close>

text \<open>
  We define the type of chains as an abstract type.
\<close>

typedecl chain

consts length :: "chain \<Rightarrow> nat" ("|_|")

subsection \<open> Specification \<close>

text \<open>
  In this section we specify the desired abstract behavior of an implementation that solves the
  chain selection problem:

    \<^item> Collect the set of all chains broadcast in the current slot.

    \<^item> Have also the current chain available.

    \<^item> Pick a longest chain. If the current chain is a longest one, pick this one; otherwise resolve
      arbitrarily.
\<close>

text \<open>
  We define a predicate to tell whether a given chain \<open>\<C>\<close> is a longest chain with respect to a
  given set of chains \<open>\<CC>\<close>.
\<close>
abbreviation is_a_longest_chain :: "chain \<Rightarrow> chain set \<Rightarrow> bool" where
  "is_a_longest_chain \<C> \<CC> \<equiv> \<forall>\<C>' \<in> \<CC>. |\<C>| \<ge> |\<C>'|"

text \<open>
  We define an abbreviation for the subset of a given set of chains \<open>\<CC>\<close> comprised by all longest
  chains in \<open>\<CC>\<close>.
\<close>
abbreviation max_chains :: "chain set \<Rightarrow> chain set" where
  "max_chains \<CC> \<equiv> {\<C> \<in> \<CC>. is_a_longest_chain \<C> \<CC>}"

text \<open>
  We define a specification function: Given a set \<open>\<CC>\<close> of collected chains throughout a slot, if \<open>\<C>\<close>
  is a longest chain then an implementation must pick \<open>\<C>\<close>, otherwise it must pick a longest one in
  \<open>\<CC>\<close>.
\<close>

definition spec :: "chain \<Rightarrow> chain set \<Rightarrow> chain set" where
  "spec \<C> \<CC> = (if is_a_longest_chain \<C> \<CC> then {\<C>} else max_chains \<CC>)"

subsection \<open> Implementation \<close>

text \<open>
  In this section we give an implementation that solves the chain selection problem. The implemented
  behavior is the following:

  \<^item> Repeatedly receive a new chain throughout the slot.

  \<^item> Update the current chain to the received one if the received one is longer.
\<close>

text \<open>
  We define a binary maximum function with a bias towards the first argument.
\<close>

fun max_chain :: "chain \<Rightarrow> chain \<Rightarrow> chain" where
  "max_chain \<C> \<C>' = (if |\<C>| \<ge> |\<C>'| then \<C> else \<C>')"

text \<open>
  We define the implementation function: Given a list \<open>\<CC>\<close> of chains modeling the arrival order of
  such chains throughout the slot and an initial current chain \<open>\<C>\<close>, this implementation processes
  \<open>\<CC>\<close> sequentially to calculate the new current chain. Since ties are broken in favor of the current
  chain, the result is the leftmost longest chain.
\<close>

definition impl :: "chain \<Rightarrow> chain list \<Rightarrow> chain" where
  "impl \<C> \<CC> = foldl max_chain \<C> \<CC>"

subsection \<open> Verification \<close>

text \<open>
  In this section we formally verify the implementation above, that is, we prove that the
  implementation satisfies the specification in the following sense: Given a list \<open>\<CC>\<close> of chains
  modeling the arrival order of such chains throughout the slot and a current chain \<open>\<C>\<close>, the choice
  of the new current chain made by the implementation after processing \<open>\<CC>\<close> meets the specification,
  i.e. if \<open>\<C>\<close> is a longest chain then the implementation picks \<open>\<C>\<close>, otherwise it picks a longest one
  in \<open>\<CC>\<close>, namely the leftmost longest one. In the latter case, this holds since the leftmost longest
  chain in \<open>\<CC>\<close> is certainly a longest one in the set comprised by the chains in \<open>\<CC>\<close>.
\<close>

theorem max_chain_choice:
  shows "impl \<C> \<CC> \<in> spec \<C> (set \<CC>)"
proof (induction \<CC> arbitrary: \<C>)
  case Nil
  then show ?case
    unfolding spec_def and impl_def by simp
next
  case (Cons \<C>' \<CC>')
  have "impl \<C> (\<C>' # \<CC>') = impl (max_chain \<C> \<C>') \<CC>'"
    unfolding impl_def by simp
  also from Cons.IH have "\<dots> \<in> spec (max_chain \<C> \<C>') (set \<CC>')"
    by blast
  also have "\<dots> \<subseteq> spec \<C> (set (\<C>' # \<CC>'))"
  proof (cases "is_a_longest_chain (max_chain \<C> \<C>') (set \<CC>')")
    case True
    then have *: "spec (max_chain \<C> \<C>') (set \<CC>') = {max_chain \<C> \<C>'}"
      unfolding spec_def by simp
    also have "\<dots> \<subseteq> spec \<C> (set (\<C>' # \<CC>'))"
    proof (cases "|\<C>| \<ge> |\<C>'|")
      case True
      with * have "spec \<C> (set (\<C>' # \<CC>')) = {\<C>}"
        unfolding spec_def
        (* TODO: Find a nicer proof. *)
        by (metis (no_types, lifting) insert_iff list.simps(15) max_chain.elims mem_Collect_eq order_refl)
      with True show ?thesis
        by simp
    next
      case False
      then have "spec \<C> (set (\<C>' # \<CC>')) = max_chains (set (\<C>' # \<CC>'))"
        unfolding spec_def by simp
      with True show ?thesis
        unfolding spec_def by auto
    qed
    finally show ?thesis .
  next
    case False
    then have **: "spec (max_chain \<C> \<C>') (set \<CC>') = max_chains (set \<CC>')"
      unfolding spec_def by auto
    also have "\<dots> \<subseteq> spec \<C> (set (\<C>' # \<CC>'))"
    proof (cases "|\<C>| \<ge> |\<C>'|")
      case True
      with False have "spec \<C> (set (\<C>' # \<CC>')) = max_chains (set (\<C>' # \<CC>'))"
        unfolding spec_def by auto
      moreover from False have "\<not>is_a_longest_chain \<C> (set (\<C>' # \<CC>'))"
        by auto
      ultimately show ?thesis
        (* TODO: Find a nicer proof. *)
        by (smt Collect_mono_iff True dual_order.trans insert_iff linear list.simps(15))
    next
      case False
      then have "spec \<C> (set (\<C>' # \<CC>')) = max_chains (set (\<C>' # \<CC>'))"
        unfolding spec_def by simp
      with ** show ?thesis
        unfolding spec_def
        (* TODO: Find a nicer proof. *)
        by (smt Ball_Collect CollectD dual_order.trans linear max_chain.simps set_ConsD set_subset_Cons singletonD subsetCE)
    qed
    finally show ?thesis .
  qed
  finally show ?case
    by blast
qed

end
