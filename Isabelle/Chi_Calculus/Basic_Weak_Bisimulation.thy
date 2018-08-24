theory Basic_Weak_Bisimulation
  imports Basic_Transition_System
begin

(* Sequence of \<tau>-transitions: \<Longrightarrow>\<^sub>\<flat> *)

abbreviation tau_sequence :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> _" [51, 0, 51] 50)
where
  "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<equiv> (P, Q) \<in> {(P, Q) | P Q. \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q}^*"

lemma tau_sequence_refl: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P" 
  by simp

lemma tau_sequence_non_empty: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q; P \<noteq> Q \<rbrakk> \<Longrightarrow> \<exists>R. \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R \<and> \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (smt Pair_inject converse_rtranclE mem_Collect_eq) 

lemma tau_sequence_trans: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by simp

lemma tau_transition_is_tau_sequence: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" 
  by auto

lemma append_tau_transition_to_tau_sequence_is_tau_sequence:  "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (metis (mono_tags, lifting) mem_Collect_eq rtrancl.simps)

lemma prepend_tau_transition_to_tau_sequence_is_tau_sequence: "\<lbrakk> \<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R; \<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (simp add: rtrancl_into_trancl2 trancl_into_rtrancl) 

lemma tau_sequence_induction[consumes 1, case_names tau_seq_refl tau_seq_step]:
  assumes "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  and     "\<PP> P"
  and     "\<And>R S. \<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S; \<PP> R \<rbrakk> \<Longrightarrow> \<PP> S"
  shows   "\<PP> Q"
  using assms
  by (induction rule: rtrancl_induct) auto 

(* The lifted operational semantics rules for \<tau>-sequences. *)
(* \<tau>-sequence relation behaves as expected w.r.t. process operators (except, of course, \<triangleright> and \<triangleleft>) *)

lemma tau_sequence_parallel_preservation_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R P')
  then have "\<Gamma> \<turnstile> R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q" 
    using tau_seq_step.hyps(2) by (simp add: acting_left)
  then show ?case 
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> Q'"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R Q')
  then have "\<Gamma> \<turnstile> P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P \<parallel> Q'" 
    using tau_seq_step.hyps(2) by (simp add: acting_right)
  then show ?case 
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

lemma tau_sequence_parallel_preservation: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'; \<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" and "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'" 
  have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
    using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> and tau_sequence_parallel_preservation_left by simp
  moreover have "\<Gamma> \<turnstile> P' \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'"
    using \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> and tau_sequence_parallel_preservation_right by simp 
  finally show ?thesis 
    by simp
qed 

lemma tau_sequence_new_channel_preservation: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<Longrightarrow> \<Gamma> \<turnstile> \<nu> a. P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<nu> a. Q"
proof (induction rule: tau_sequence_induction)
  case tau_seq_refl
  then show ?case by simp
next
  case (tau_seq_step R P')
  then have "\<Gamma> \<turnstile> \<nu> a. R  \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> \<nu> a. P'"
    using tau_seq_step(2) by (simp add: acting_scope)
  then show ?case 
    using tau_seq_step.IH and append_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed  

lemma tau_sequence_invocation_preservation: "\<lbrakk> \<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q; \<Gamma> N V \<noteq> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
proof -
  assume "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" and "\<Gamma> N V \<noteq> Q"
  then obtain R where Tran: "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R" and Seq: "\<Gamma> \<turnstile> R \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q" 
    using tau_sequence_non_empty by blast
  then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> R"
    using Tran and invocation by fastforce
  then show ?thesis
   using Seq and prepend_tau_transition_to_tau_sequence_is_tau_sequence by simp
qed

(* Weak Semantics *)

(** Weak basic transition \<Longrightarrow>\<^sub>\<flat>C **)
(** NOTE: Note that even though the transition P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a appears to contain a binder into \<Q> a, in
reality it does not. The binder occurs inside the definition, where a binds into \<P> a. The process 
\<P> a then does a \<tau>-sequence to \<Q> a, which "a" does not bind into, unless \<P> a = \<Q> a. Formally, one can 
still reason about "a" as a binder: there is no way that any new names can be introduced by a \<tau>-sequence; 
the name "a" can be communicated within the process, but if so it occurs free in an output-prefix in P. **)
(** TODO: Perhaps I can define a weak basic transition without using a residual, i.e. as
 weak_basic_transition :: process \<Rightarrow> process \<Rightarrow> [IO action|chan] \<Rightarrow> process **)

definition 
  weak_basic_transition :: "
    ('name \<Rightarrow> 'val \<Rightarrow> ('name, 'chan, 'val) process) \<Rightarrow>
    ('name, 'chan, 'val) process \<Rightarrow>
    ('name, 'chan, 'val) basic_residual \<Rightarrow>
    bool"
  ("_ \<turnstile> _ \<Longrightarrow>\<^sub>\<flat>_" [51, 0, 51] 50)
  where
   "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>C \<equiv> 
      case C of 
        \<lbrace>\<alpha>\<rbrace> Q     \<Rightarrow> \<exists>R S. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> \<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q |
        Opening \<Q> \<Rightarrow> \<exists>R \<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a)"

lemma weak_basic_transition_acting_intro: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S; \<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_basic_transition_def by force 

lemma weak_basic_transition_scoping_intro: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R; \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a; \<And>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_basic_transition_def by force 

lemma weak_basic_transition_acting_elim: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<exists>R S. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<and> \<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q"
  by (simp split: basic_residual.split add: weak_basic_transition_def)

lemma weak_basic_transition_scoping_elim: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<exists>R \<P>. \<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<and> \<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<and> (\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a)"
  by (simp split: basic_residual.split add: weak_basic_transition_def)

lemma weak_basic_transition_single_acting: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q"
  using weak_basic_transition_acting_intro by blast 

lemma weak_basic_transition_single_scoping: "\<Gamma> \<turnstile> P \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  using weak_basic_transition_scoping_intro by blast

(** Lifted weak basic operational semantics **)

lemma weak_basic_transition_sending: "\<Gamma> \<turnstile> m \<triangleleft> V \<Longrightarrow>\<^sub>\<flat>\<lbrace>m \<triangleleft> V\<rbrace> send_cont m V"
  using weak_basic_transition_def and sending by force

lemma weak_basic_transition_receiving: "\<Gamma> \<turnstile> m \<triangleright> x. \<P> x \<Longrightarrow>\<^sub>\<flat>\<lbrace>m \<triangleright> V\<rbrace> \<P> V"
  using weak_basic_transition_def and receiving by force 

lemma weak_basic_transition_communication: "\<lbrakk> \<eta> \<bowtie> \<mu>; \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'; \<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q' \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
proof -
  assume "\<eta> \<bowtie> \<mu>" and "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'" and "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'"
  then obtain R and S where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'"
    using weak_basic_transition_acting_elim and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> P'\<close> by fastforce
  moreover obtain T and U where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> T" and "\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> U" and "\<Gamma> \<turnstile> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'"
    using weak_basic_transition_acting_elim and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> Q'\<close> by fastforce
  ultimately show ?thesis
  proof -
    have "\<Gamma> \<turnstile> R \<parallel> T \<longmapsto>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> S \<parallel> U" 
      using \<open>\<eta> \<bowtie> \<mu>\<close> and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<eta>\<rbrace> S\<close> and \<open>\<Gamma> \<turnstile> T \<longmapsto>\<^sub>\<flat>\<lbrace>IO \<mu>\<rbrace> U\<close> using communication by fastforce
    moreover have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> T" 
      using \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> T\<close> and tau_sequence_parallel_preservation by simp
    moreover have "\<Gamma> \<turnstile> S \<parallel> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q'" 
      using \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> and \<open>\<Gamma> \<turnstile> U \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> and tau_sequence_parallel_preservation by simp
    ultimately show "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<tau>\<rbrace> P' \<parallel> Q'"
      using weak_basic_transition_acting_intro by simp
  qed
qed

lemma weak_basic_transition_opening: "\<Gamma> \<turnstile> \<nu> a. \<P> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  by (simp add: opening weak_basic_transition_single_scoping)

lemma weak_basic_transition_invocation: "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C \<Longrightarrow> \<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sub>\<flat>C"
proof (cases C)
  assume "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C"
  case (Acting \<alpha> P)
  then obtain R and S where "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P" 
    using weak_basic_transition_acting_elim and \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C\<close> by fastforce
  then show ?thesis
  proof (cases "\<Gamma> N V = R")
    case True
    then have "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S"
      using \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by simp
    then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S"
      by (simp add: invocation)
    moreover have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<langle>N\<rangle> V" 
      by (simp add: tau_sequence_refl)
    ultimately show ?thesis 
      using Acting and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<close> and weak_basic_transition_acting_intro by blast
  next
    case False
    then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R"
      using \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and tau_sequence_invocation_preservation by simp
    then show ?thesis
      using Acting and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P\<close> and weak_basic_transition_acting_intro
      by blast 
  qed
next
  assume "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C"
  case (Opening \<P>)
  then obtain R and \<Q> where "\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a"
    using weak_basic_transition_scoping_elim and \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sub>\<flat>C\<close> by fastforce
  then show ?thesis 
  proof (cases "\<Gamma> N V = R")
    case True
      then have "\<Gamma> \<turnstile> \<Gamma> N V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
        using \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> by simp
      then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
        by (simp add: invocation)
      moreover have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<langle>N\<rangle> V" 
        by (simp add: tau_sequence_refl)
      ultimately show ?thesis 
        using Opening and \<open>\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> and weak_basic_transition_scoping_intro by blast
  next
    case False
      then have "\<Gamma> \<turnstile> \<langle>N\<rangle> V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R"
        using \<open>\<Gamma> \<turnstile> \<Gamma> N V \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> and tau_sequence_invocation_preservation by simp
      then show ?thesis
        using Opening and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> and \<open>\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> and weak_basic_transition_scoping_intro
        by blast 
  qed
qed

lemma weak_basic_transition_acting_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P' \<parallel> Q"
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P'"
  then obtain R and S where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'" 
    using weak_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> Q"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S \<parallel> Q"
    using acting_left and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> S \<parallel> Q  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P' \<parallel> Q"
    using tau_sequence_parallel_preservation_left and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P'\<close> by simp
  ultimately show ?thesis 
    by (simp add: weak_basic_transition_acting_intro)
qed

lemma weak_basic_transition_acting_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q' \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> Q'"
proof -
  assume "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> Q'"
  then obtain R and S where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S" and "\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'" 
    using weak_basic_transition_acting_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> R"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> P \<parallel> S"
    using acting_right and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> S\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> P \<parallel> S  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> Q'"
    using tau_sequence_parallel_preservation_right and \<open>\<Gamma> \<turnstile> S \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> Q'\<close> by simp
  ultimately show ?thesis 
    by (simp add: weak_basic_transition_acting_intro)
qed

lemma weak_basic_transition_opening_left: "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a \<parallel> Q"  
proof -
  assume "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a"
  then obtain R and \<Q> where "\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a" and "\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a" 
    using weak_basic_transition_scoping_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R \<parallel> Q"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> P \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> R \<parallel> Q \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<parallel> Q"
    using opening_left and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a\<close> by fastforce
  moreover have "\<And>a. \<Gamma> \<turnstile> \<Q> a \<parallel> Q  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a \<parallel> Q"
    using tau_sequence_parallel_preservation_left and \<open>\<forall>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<P> a\<close> by fastforce
  ultimately show ?thesis 
    by (simp add: weak_basic_transition_scoping_intro)
qed

lemma weak_basic_transition_opening_right: "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a \<Longrightarrow> \<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<Q> a"  
proof -
  assume "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a"
  then obtain R and \<P> where "\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R" and "\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a" and "\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a" 
    using weak_basic_transition_scoping_elim by fastforce
  then have "\<Gamma> \<turnstile> P \<parallel> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> R"
    using tau_sequence_parallel_preservation and \<open>\<Gamma> \<turnstile> Q \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> R\<close> by fastforce
  moreover have "\<Gamma> \<turnstile> P \<parallel> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> P \<parallel> \<P> a"
    using opening_right and \<open>\<Gamma> \<turnstile> R \<longmapsto>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<P> a\<close> by fastforce
  moreover have "\<And>a. \<Gamma> \<turnstile> P \<parallel> \<P> a  \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> P \<parallel> \<Q> a"
    using tau_sequence_parallel_preservation_right and \<open>\<forall>a. \<Gamma> \<turnstile> \<P> a \<Longrightarrow>\<^sup>\<tau>\<^sub>\<flat> \<Q> a\<close> by fastforce
  ultimately show ?thesis 
    by (simp add: weak_basic_transition_scoping_intro)
qed

(* TODO: Prove. *)
lemma weak_basic_transition_scoped_acting: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<R> a \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<alpha>\<rbrace> \<nu> a. \<R> a"
  sorry

(* TODO: Prove. *)
lemma weak_basic_transition_scoped_opening: "\<lbrakk> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> a\<rbrace> \<Q> a; \<And>a. \<Gamma> \<turnstile> \<Q> a \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<R> a b \<rbrakk> \<Longrightarrow> \<Gamma> \<turnstile> P \<Longrightarrow>\<^sub>\<flat>\<lbrace>\<nu> b\<rbrace> \<nu> a. \<R> a b"
  sorry

end
